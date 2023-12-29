{-# LANGUAGE ScopedTypeVariables, ImplicitParams #-}
module Sigil.Interpret.Term
  ( Term(..) ) where

import Prelude hiding (head, lookup)
import Control.Monad((<=<))
import Control.Monad.Except (MonadError, throwError)
import Data.Kind
import Data.Maybe
import Data.Text (Text)
import Data.Foldable (find)
import Data.Map (Map)

import Prettyprinter

import Sigil.Abstract.Names
import Sigil.Abstract.Environment
import Sigil.Abstract.AlphaEq
import Sigil.Concrete.Internal
import Sigil.Concrete.Decorations.Implicit
  

{------------------------------ THE TERM CLASSES -------------------------------}
{- The Term represents types which can be normalized/evaluated. As such, it    -}
{- supports two primary methods:                                               -}
{- • normalize: convert to canonical (Β-normal, η-long) form                   -}
{- • equiv: αβη equivalence                                                    -}
{-                                                                             -}
{-------------------------------------------------------------------------------}


class Term a where
  normalize :: (MonadError err m, MonadGen m) => (Doc ann -> err) -> Env (Maybe a,a) -> a -> a -> m a
  equiv :: (MonadError err m, MonadGen m) => (Doc ann -> err) -> Env (Maybe a,a) -> a -> a -> a -> m Bool


{------------------------------- IMPLEMENTATION --------------------------------}
{- Currently, the only type which implements the term typeclass is             -}
{- InternalCore. The implementation uses a strategy of Normalization by        -}
{- Evaluation, based on an algorithm described in the paper 'Normalization by  -}
{- Evaluation, Dependent Types and Impredicativity' by Andreas Abel.           -}
{-                                                                             -}
{- DENOTATIVE TERMS (Sem m e)                                                  -}
{----------------------------                                                  -}
{- These are types for a denotative interpretation of expressions in core:     -}
{- Most look similar to their 'normal' semantic representation, with the       -}
{- important exception of functions, which are represented as closures,        -}
{- capturing their environment.                                                -}
{-                                                                             -}
{- There are also types for Neutral and Normal terms, which are terms that     -}
{- have been evaluated as much as is possible. Normal Terms have the form of   -}
{- a λ-abstraction, Π-type Universe or Constant. Importantly, normal terms are -}
{- accompanied by their type. Neutral terms are those whose evaluation is      -}
{- blocked because of an uninstantiated variable, e.g. f 2, where f is an      -}
{- uninstantiated variable.                                                    -}
{-                                                                             -}
{-------------------------------------------------------------------------------}


data Sem m
  = SUni Integer
  | SPrd ArgType Name (Sem m) (Sem m)
  | SAbs Name (Sem m) (Sem m -> m (Sem m))
  | SInd Name (Sem m) [(Text, Sem m -> m (Sem m))]
  | SCtr Text (Sem m) [Sem m]
  | SEql (SemTel m) (Sem m) (Sem m) (Sem m)
  | SDap (SemTel m) (Sem m)
  | STrL (SemTel m) (Sem m) (Sem m)
  | STrR (SemTel m) (Sem m) (Sem m)
  | Neutral (Sem m) (Neutral m)

data Neutral m
  = NeuVar Name
  | NeuApp (Neutral m) (Normal m)
  | NeuDap (SemTel m) (Neutral m) -- A neutral explicit substitution, must be empty!
  | NeuRec Name (Sem m) (Neutral m)
    [(Sem m -> Maybe (m (Sem m)), m (Pattern Name, Sem m))]

data Normal (m :: Type -> Type) = Normal (Sem m) (Sem m)

type SemTel m = [(Name, (Sem m, Sem m, Sem m), Sem m)]

{-------------------------------- TERM INSTANCE --------------------------------}
{- The term instance for Core applies type directed normalization by           -}
{- evaluation. Equality is derived from the Eq instance defined in Core.hs,    -}
{- extended to first perform normalization.                                    -}
{-                                                                             -}
{- Normalization relies on a few key helper functions:                         -}
{- • eval performs untyped evaluation, converting any term into a Semantic  e  -}
{-   term. eval has a helper function, app, which performs both function and   -}
{-   type application.                                                         -}
{- • env_eval evaluates each term in an environment, returning a semantic      -}
{-   environment.                                                              -}
{- • read_nf takes a term in normal form, and reads it back into a Core term.  -}
{-   this is type-directed because all normal terms have an accompanying type. -}
{- • read_ne takes a term in netural form, and reads it back into a Core term. -}
{-                                                                             -}
{-------------------------------------------------------------------------------}


instance Term InternalCore where
  normalize lift_error env ty term =
    let ?lift_err = lift_error in
      let ty' = eval ty =<< env_eval env
          term' = eval term =<< env_eval env
      in read_nf =<< (Normal <$> ty' <*> term')


  equiv lift_error env ty x y = do
    αeq <$> normalize lift_error env ty x <*> normalize lift_error env ty y
    where 
      ?lift_err = lift_error


read_nf :: forall err ann m. (MonadError err m, MonadGen m, ?lift_err :: Doc ann -> err) => Normal m -> m InternalCore
read_nf (Normal ty val) = case (ty, val) of 
  -- Values
  (SPrd at name a b, f) -> do
    let
      fnc_name = (maybe name id (get_name f))
      neua = Neutral a $ NeuVar name
      neuvar = Neutral a $ NeuVar fnc_name
      lvl = uni_level a

    a' <- read_nf $ Normal (SUni lvl) a
    f' <- read_nf =<< (Normal <$> (b `app` neua) <*> (f `app` neuvar))
    pure $ Abs at (bind fnc_name a') f'

  -- TODO: figure out what to do with SDap telescope?!
  (SEql tel ty _ _, SDap _ val) -> do
    Dap <$> read_tel tel <*> read_nf (Normal ty val)
    where
      read_tel = mapM (\(nm, (ty, l, r), prf) -> do
                          ity <- read_nf (Normal (SUni $ uni_level ty) ty)
                          il <- read_nf (Normal ty l)
                          ir <- read_nf (Normal ty r)
                          iprf <- read_nf (Normal (SEql [] ty l r) prf)
                          pure $ (AnnBind (nm, (ity, il, ir)), iprf))

  -- Types
  (SUni _, SUni i) -> pure $ Uni i
  (SUni k, SPrd at name a b) -> do
    let neua :: Sem m
        neua = Neutral a $ NeuVar name
    a' <- (read_nf $ Normal (SUni k) a)
    b' <- (read_nf =<< Normal (SUni k) <$> (b `app` neua))
    pure $ Prd at (bind name a') b'
  (SUni k, SEql tel ty a a') -> do
    let read_nf_tel _ out [] = pure out
        read_nf_tel in_tel out ((name, (ty, v1, v2), id) : tel) = do 
          ty' <- read_nf (Normal (SUni k) ty)
          v1' <- read_nf (Normal ty v1)
          v2' <- read_nf (Normal ty v2)
          id' <- read_nf (Normal (SEql in_tel ty v1 v2) id)
          read_nf_tel (in_tel <> [(name, (ty, v1, v2), id)]) (out <> [(bind name (ty', v1', v2'), id')]) tel
    Eql <$> read_nf_tel [] [] tel
      <*> read_nf (Normal (SUni k) ty)
      <*> read_nf (Normal ty a)
      <*> read_nf (Normal ty a')
  (SUni k, SInd iname ity ctors) -> do
    let read_nf_ctor (label, fnc) = 
          (label, )
            <$> (read_nf . (Normal (SUni k)) =<< fnc (Neutral ity (NeuVar iname)))
    Ind iname
      <$> read_nf (Normal (SUni k) ity)
      <*> mapM read_nf_ctor ctors
  (SInd nm ty ctors, SCtr label _ vals) -> do
    ind_ty <- read_nf (Normal ty (SInd nm ty ctors))
    
    case find ((== label) . fst) ctors of
      Just (_, cty) -> do
        cty' <- cty $ SInd nm ty ctors
        recur (Ctr label ind_ty) cty' (reverse vals)
        where
          recur v _ [] = pure v
          recur v (SPrd _ _ a b) (val:vals) = do
            b' <- b `app` val
            val' <- read_nf (Normal a val)
            recur (App v val') b' vals
          recur _ _ _ = throw "recur unequal!"
      Nothing -> throw $ "Constructor cannot be found!"
        
  (_, Neutral _ e) -> read_ne e 
  (_, _) -> throw ("bad read_nf:" <+> pretty val <+> "⮜" <+> pretty ty)


read_ne :: (MonadError err m, MonadGen m, ?lift_err :: Doc ann -> err) => Neutral m -> m InternalCore
read_ne neu = case neu of 
  NeuVar name -> pure $ Var name
  NeuApp l r -> App <$> (read_ne l) <*> (read_nf r)
  NeuDap tel val -> Dap <$> read_tel tel <*> read_ne val
    where
      read_tel = mapM (\(nm, (ty, l, r), prf) -> do
                          ity <- read_nf (Normal (SUni $ uni_level ty) ty)
                          il <- read_nf (Normal ty l)
                          ir <- read_nf (Normal ty r)
                          iprf <- read_nf (Normal (SEql [] ty l r) prf)
                          pure $ (AnnBind (nm, (ity, il, ir)), iprf))
  NeuRec nm ty val cases -> do
    ty' <- read_nf (Normal (SUni $ uni_level ty) ty)
    (_, a, b) <- case ty of
      SPrd _ rnm a b -> pure (rnm, a, b)
      _ -> throw "bad read_ne in recursive"
    b' <- b `app` a
    val'<- read_ne val
    let read_case (_, m) = do
          (ptn, core) <- m
          core' <- read_nf (Normal b' core)
          pure $ (ptn, core')
    cases' <- mapM read_case cases
    pure $ Rec (AnnBind (nm, ty')) val' cases'


eval :: forall m err ann. (MonadError err m, MonadGen m, ?lift_err :: Doc ann -> err) => InternalCore -> Map Name (Sem m) -> m (Sem m)
eval term env = case term of
  Uni n -> pure $ SUni n
  Prd at bnd b -> do
    nm <- fromMaybe (throw "Prd must bind a name") (fmap pure $ name bnd)
    a <- fromMaybe (throw "Prd must bind a type") (fmap pure $ tipe bnd)
    a' <- eval a env
    pure $ SPrd at nm a' $ SAbs nm a' (\val -> eval b (insert nm val env))
  Var name -> lookup_err ?lift_err name env
  Abs _ bnd body -> do
    nme <- fromMaybe (throw "Abs must bind a name") (fmap pure $ name bnd)
    ty <- fromMaybe (throw "Abs must bind a type") (fmap pure $ tipe bnd)
    SAbs nme <$> eval ty env <*> pure (\val -> eval body (insert nme val env))
  App l r -> do
    l' <- (eval l env)
    r' <- (eval r env)
    app l' r'

  Ind inm ity ctors -> do 
    ity' <- eval ity env
    -- let env' = 
    let ctors' = fmap (\(lbl, a) ->
                       (lbl, (\val -> eval a (insert inm val env))))
                ctors
    pure $ SInd inm ity' ctors'

  Ctr label ty -> SCtr label <$> (eval ty env) <*> pure []
  Rec (AnnBind (rname, rty)) val cases -> do
    rty' <- eval rty env
    (at, pname, a, b) <- case rty' of 
      SPrd at pname a b -> pure (at, pname, a, b)
      _ -> throw "Rec fn must have product type"
    let rec_fn = SAbs pname a (\val -> recur env rname (SPrd at pname a b) val cases')
        cases' = (map to_case_fn cases)

        to_case_fn (pat, core) =
          ( \val -> fmap (\env' -> (eval core (insert rname rec_fn env'))) (match env pat val)
          , ((pat,) <$> (eval core =<< (insert rname (Neutral rty' (NeuVar rname)) <$> match_neu env pat a)))
          )

        match :: Map Name (Sem m) -> Pattern Name -> Sem m -> Maybe (Map Name (Sem m))
        match env (PatVar n) v = Just $ insert n v env
        match env (PatCtr n subpats) (SCtr n' _ vals)
          | n == n' = foldl (\menv (p, v) -> do -- TODO: check that foldl is corect!
                                env <- menv
                                match env p v) (Just env) (zip subpats vals)
          | otherwise = Nothing
        match _ _ _ = Nothing

        match_neu :: Map Name (Sem m) -> Pattern Name -> Sem m -> m (Map Name (Sem m))
        match_neu env (PatVar n) ty = pure $ insert n (Neutral ty (NeuVar n)) env
        match_neu env (PatCtr label subpats) (SInd _ _ ctors) = do
          -- args <- ty_args label ctors
          let ty_args = \case -- TODO: borked! include name!
                (SPrd _ _ a b) -> [a] <> ty_args b
                _ -> []
          args <- case find ((== label) . fst) ctors of
            Just (_, ty) -> ty_args <$> ty (Neutral rty' (NeuVar rname))
            Nothing -> throw "bad pattern match"
          foldl (\m (pat, arg) -> m >>= \env -> match_neu env pat arg) (pure env) (zip subpats args)
        match_neu _ _ ty = throw ("bad type in match_neu:" <+> pretty ty)
    val' <- eval val env
    recur env rname (SPrd at pname a b) val' cases' 
  
  Eql tel ty v1 v2 -> do
    -- Eql evaluation is divided into three phases:
    -- Phase 1: eliminate all instances of ρ (refl) from the telescope
    -- Phase 2: perform all ty eliminations
    -- Phase 3: eliminate unused bindings

    -- Extract reflections
    -- TODO: eliminate unused binds
    (tel_sem, env') <- eval_tel env tel
    ty_sem <- eval ty env'
    eql env' tel_sem ty_sem v1 v2
    -- TODO: phase 3!!
    -- pure $ SEql tel' ty' v1' v2'

  Dap tel val -> do
    (tel', env') <- eval_tel env tel
    val' <- eval val env'
    dap env tel' val' 

  TrL tel ty val -> do
    (tel', env') <- eval_tel env tel
    ty' <- eval ty env'
    val' <- eval val env'
    eval_over env' STrL tel' ty' val'
  TrR tel ty val -> do
    (tel', env') <- eval_tel env tel
    ty' <- eval ty env'
    val' <- eval val env'
    eval_over env' STrR tel' ty' val'
  -- LfL tel ty val -> eval_over env LfL tel ty val
  -- LfR tel ty val -> eval_over env LfR tel ty val
  -- Implicit terms 
  TyCon _ _ _ -> throw "don't know how to eval tycon"

{-------------------------------------------------------------------------------}
{-                                                                             -}
{-------------------------------------------------------------------------------}

eval_over :: forall m err ann. (MonadError err m, MonadGen m, ?lift_err :: Doc ann -> err)
  => Map Name (Sem m) -> (SemTel m -> Sem m -> Sem m -> Sem m)
    -> SemTel m -> Sem m -> Sem m -> m (Sem m) 
eval_over env ctor tel ty val = do
  -- reduce over type families
  case ty of 
    SPrd _ name a fnc -> do
      u <- fresh_varn "u"
      v <- fresh_varn "v"
      id <- fresh_varn "id"
      -- TODO: subst left of tel in u
      -- aleft <- eval_sem (foldl (\env (nm, (_, l, _), _) -> insert nm l env) env tel) a
      -- aright <- eval_sem (foldl (\env (nm, (_, _, r), _) -> insert nm r env) env tel) a
      pure (SAbs u a
            (\uval ->
               pure $ SAbs v a
               (\vval -> 
                  pure $ SAbs id (SEql [] a uval vval)
                  (\idval -> do
                     ty' <- fnc `app` (Neutral a (NeuVar name))
                     val' <- val `app` (Neutral a (NeuVar name))
                     eval_over (insert id idval . insert v vval . insert u uval $ env)
                       ctor (tel <> [(name, (a, uval, vval), idval)])
                       ty' val'))))
    SUni _ -> pure $ ctor tel ty val
    SInd _ _ _ ->
      throw ("Don't know how to reduce over type:" <+> pretty ty)
    _ -> throw ("over expects a type as first value, got:" <+> pretty ty)

eval_tel :: forall m err ann. (MonadError err m, MonadGen m, ?lift_err :: Doc ann -> err)
  => Map Name (Sem m) -> [(AnnBind Name (InternalCore, InternalCore, InternalCore), InternalCore)]
    -> m ([(Name, (Sem m, Sem m, Sem m), Sem m)], Map Name (Sem m))
eval_tel env [] = pure ([], env)
eval_tel env ((bnd, id) : tel) = do 
  name <- fromMaybe (throw "Eql Telescope must bind a name") (fmap pure $ name bnd)
  id' <- eval id env
  case id' of 
    -- TODO: what about when tel is non-empty??
    SDap [] val -> 
      eval_tel (insert name val env) tel
    _ -> do
      (ty, v1, v2) <- fromMaybe (throw "Eql Telescope must bind an equality") (fmap pure $ tipe bnd)
      ty' <- eval ty env 
      v1' <- eval v1 env 
      v2' <- eval v2 env 

      -- TODO: inserting neutral terms into environment may be bad!!
      --       (normally we only do this at the read_nf stage!)
      (tel', env') <- eval_tel (insert name (Neutral ty' (NeuVar name)) env) tel
      pure $ ((name, (ty', v1', v2'), id') : tel', env')


eval_stel :: forall m err ann
  . (MonadError err m, MonadGen m, ?lift_err :: Doc ann -> err)
  => Map Name (Sem m) -> SemTel m -> m (SemTel m, Map Name (Sem m))
eval_stel env tel = go env tel [] where 
  go :: Map Name (Sem m) -> SemTel m -> SemTel m -> m (SemTel m, Map Name (Sem m))
  go env ((name, (ity, v1, v2), id) : tel) tel_out = do
    id' <- eval_sem env id
    -- Note: telescopes over refl reduce to regular equalities
    -- TODO: what to to if dap telescope is non-empty?
    case id' of
      SDap [] val ->
        go (insert name val env) tel tel_out
      _ -> do
        ity' <- eval_sem env ity
        v1' <- eval_sem env v1
        v2' <- eval_sem env v2  
        -- TODO: inserting neutral terms into environment may be bad!!
        --       (normally we only do this at the read_nf stage!)
        go env tel ((name, (ity', v1', v2'), id') : tel_out)
  go env [] tel_out = pure (reverse tel_out, env)


{-------------------------------------------------------------------------------}
{-                                                                             -}
{-                                                                             -}
{-                                                                             -}
{-                                                                             -}
{-------------------------------------------------------------------------------}

-- Evaluates an identity telescope at the term level
-- eval_tel tel_out tel_in ty ty_vals tm_vals
-- Used in Dap, TrL, TrR
--eval_tm_tel tel_out [] val ty_terms val_terms = case val of 

eval_sem :: forall m err ann. (MonadError err m, MonadGen m, ?lift_err :: Doc ann -> err) => Map Name (Sem m) -> (Sem m) -> m (Sem m)
eval_sem env term = case term of
  SUni n -> pure $ SUni n
  SPrd at n a b -> do
    a' <- eval_sem env a
    pure $ SPrd at n a' $ SAbs n a' (eval_sem env <=< app b)
  SAbs n a f -> do
    pure $ SAbs n a (eval_sem env <=< f)
  SEql tel ty v1 v2 -> do
    (tel_sem, env') <- eval_stel env tel 
    ty_sem <- eval_sem env ty   
    seql env' tel_sem ty_sem v1 v2
  SDap tel val -> do
    (tel_sem, env') <- eval_stel env tel
    SDap tel_sem <$> eval_sem env' val
  SInd nm ty ctors -> SInd nm <$> eval_sem env ty <*> pure (map (\(l, fnc) -> (l, eval_sem env <=< fnc)) ctors)
  SCtr label ty vals -> SCtr label <$> eval_sem env ty <*> mapM (eval_sem env) vals
  STrL tel ty val -> do
    (tel', env') <- eval_stel env tel
    ty' <- eval_sem env' ty 
    val' <- eval_sem env' val 
    eval_over env' STrL tel' ty' val'
  STrR tel ty val -> do
    (tel', env') <- eval_stel env tel
    ty' <- eval_sem env' ty 
    val' <- eval_sem env' val 
    eval_over env' STrR tel' ty' val'
  Neutral _ val -> eval_neusem env val 


eval_neusem :: forall m err ann. (MonadError err m, MonadGen m, ?lift_err :: Doc ann -> err) => Map Name (Sem m) -> (Neutral m) -> m (Sem m)
eval_neusem env neu = case neu of 
  NeuVar n -> lookup_err ?lift_err n env
  NeuApp l (Normal _ r) -> do
    l' <- eval_neusem env l
    r' <- eval_sem env r
    l' `app` r'
  -- TODO: eval_neutel
  NeuDap tel v -> dap env tel =<< eval_neusem env v
  NeuRec name ty neu cases -> do 
    ty' <- eval_sem env ty
    neu' <- eval_neusem env neu
    recur env name ty' neu' cases -- TODO: cases'
      

app :: (MonadError err m, MonadGen m, ?lift_err :: Doc ann -> err) => (Sem m) -> (Sem m) -> m (Sem m)
app (SAbs _ _ fnc) val = fnc val
app (SCtr label ty vals) v =
  pure $ SCtr label ty (v : vals)
app (Neutral (SPrd _ _ a b) neu) v =
  Neutral <$> (b `app` v) <*> pure (NeuApp neu (Normal a v))
app l r = throw ("bad args to app:" <+> pretty l <+> "and" <+> pretty r) 

dap :: (MonadError err m, MonadGen m, ?lift_err :: Doc ann -> err) => Map Name (Sem m) -> SemTel m -> (Sem m) -> m (Sem m)
dap env tel term = case term of
  Neutral ty neu -> pure $ Neutral (SEql tel ty (Neutral ty neu) (Neutral ty neu)) (NeuDap tel neu)
  SAbs name a fnc -> do
    u <- fresh_varn "u"
    v <- fresh_varn "v"
    id <- fresh_varn "id"
    pure (SAbs u a
          (\uval ->
             pure $ SAbs v a
             (\vval -> 
                pure $ SAbs id (SEql [] a uval vval)
                (\idval -> do
                   res <- fnc idval
                   dap (insert id idval . insert v vval . insert u uval $ env)
                       (tel <> [(name, (a, uval, vval), idval)])
                       res))))
  SUni n -> pure $ SDap [] $ SUni n
  SCtr _ _ _ -> throw ("Currently implementing dap for constructors")
  _ -> throw ("Don't know how to dap:" <+> pretty term)

eql :: (MonadError err m, MonadGen m, ?lift_err :: Doc ann -> err) => Map Name (Sem m) -> SemTel m -> Sem m
  -> InternalCore -> InternalCore -> m (Sem m)
eql env tel tipe v1 v2 = case tipe of
  Neutral _ _ -> SEql tel tipe <$> eval v1 env <*> eval v2 env -- TODO: is this neutral??
  SPrd at name a fnc -> do
    u <- fresh_varn "u"
    v <- fresh_varn "v"
    id <- fresh_varn "id"
    -- TODO: subst left of tel in u
    aleft <- eval_sem (foldl (\env (nm, (_, l, _), _) -> insert nm l env) env tel) a
    aright <- eval_sem (foldl (\env (nm, (_, _, r), _) -> insert nm r env) env tel) a
    pure (SPrd at u aleft $ SAbs u aleft
           (\uval ->
             pure $ SPrd at v aright $ SAbs v aright
             (\vval -> do
               eqty <- seql (insert u uval . insert v vval $ env) tel a uval vval
               pure $ SPrd at id eqty (SAbs id eqty
                 (\idval -> do
                     b <- fnc `app` (Neutral a (NeuVar name)) -- TODO: I think this is wrong?
                     eql (insert u uval . insert v vval . insert id idval . insert name (Neutral a (NeuVar name)) $ env)
                      (tel <> [(name, (a, uval, vval), idval)])
                      b (App v1 (Var u)) (App v2 (Var v)))))))
  SUni n -> SEql tel (SUni n) <$> eval v1 env <*> eval v2 env
  -- SInd nm sort ctors -> do
    -- let update_ctor = \case
    --       (SPrd nm a b) = SPrd nm (to_eq a) 
    --       t -> t

    -- pure $ SInd nm sort ctors'
  SInd _ _ _ ->
    throw ("Don't know how to reduce ι at type:" <+> pretty tipe)
  _ -> throw ("ι expects a type as first value, got:" <+> pretty tipe)


recur :: (MonadError err m, MonadGen m, ?lift_err :: Doc ann -> err)
  => Map Name (Sem m) -> Name -> Sem m -> Sem m -> [(Sem m -> Maybe (m (Sem m)), m (Pattern Name, Sem m))] -> m (Sem m)
recur _ rname rty@(SPrd _ _ _ b) val cases =
    case val of 
      SCtr _ _ _ -> case find (isJust) (map (($ val) . fst) cases) of 
        Just (Just m) -> m
        _ -> throw "failed to match"
      Neutral _ neuval -> 
        Neutral <$> (b `app` val) <*> pure (NeuRec rname rty neuval cases)
      _ -> throw "recur must induct over a constructor"
recur _ _ _ _ _ = throw "recur expects recursive type to be fn" 

seql :: (MonadError err m, MonadGen m, ?lift_err :: Doc ann -> err) => Map Name (Sem m) -> [(Name, (Sem m, Sem m, Sem m), Sem m)] -> Sem m
  -> Sem m -> Sem m -> m (Sem m)
seql env tel tipe v1 v2 = case tipe of
  Neutral _ _ -> SEql tel tipe <$> eval_sem env v1 <*> eval_sem env v2 -- TODO: is this neutral??
  SPrd at name a fnc -> do
    u <- fresh_varn "u"
    v <- fresh_varn "v"
    id <- fresh_varn "id"
    -- TODO: subst left of tel in u
    aleft <- eval_sem (foldl (\env (nm, (_, l, _), _) -> insert nm l env) env tel) a
    aright <- eval_sem (foldl (\env (nm, (_, _, r), _) -> insert nm r env) env tel) a
    pure (SPrd at u aleft $ SAbs u aleft
           (\uval ->
             pure $ SPrd at v aright $ SAbs v aright
             (\vval -> do
               eqty <- (seql (insert u uval . insert v vval $ env) tel a uval vval)
               pure $ SPrd at id eqty (SAbs id eqty
                 (\idval -> do
                     b <- fnc `app` (Neutral a (NeuVar name)) -- TODO: I think this is wrong?
                     v1' <- v1 `app` uval
                     v2' <- v2 `app` vval 
                     seql (insert u uval . insert v vval . insert id idval . insert name (Neutral a (NeuVar name)) $ env)
                      (tel <> [(name, (a, uval, vval), idval)])
                      b v1' v2')))))
  SUni n -> SEql tel (SUni n) <$> eval_sem env v1 <*> eval_sem env v2
  SInd _ _ _  -> throw ("Don't know how to reduce ι at type:" <+> pretty tipe)
  _ -> throw ("ι must reduce on type, got:" <+> pretty tipe)

env_eval :: (MonadError err m, MonadGen m, ?lift_err :: Doc ann -> err) => Env (Maybe InternalCore, InternalCore) -> m (Map Name (Sem m))
env_eval = eval_helper ?lift_err eval_var 
  where
    eval_var :: (MonadError err m, MonadGen m, ?lift_err :: Doc ann -> err) =>
                Map Name (Sem m) -> Name -> (Maybe InternalCore, InternalCore) -> m (Sem m)
    eval_var env n (Nothing, ty) = mkvar env n ty
    eval_var env _ (Just val, _) = eval val env
    
    mkvar :: (MonadError err m, MonadGen m, ?lift_err :: Doc ann -> err) =>
              Map Name (Sem m) -> Name -> InternalCore -> m (Sem m)
    mkvar env n ty = do
      ty' <- eval ty env
      pure $ Neutral ty' (NeuVar n)
  
-- TODO: fix this function - it is wrong!
uni_level :: Sem m -> Integer
uni_level sem = case sem of 
  SUni n -> n
  SPrd _ _ l r -> max (uni_level l) (uni_level r)
  SAbs _ _ _ -> 0
  SEql _ ty _ _ -> uni_level ty
  SDap _ val -> uni_level val
  SInd _ ty _ -> uni_level ty
  SCtr _ _ _ -> -1 -- do values have universe levels?
  STrL _ _ _ -> -1
  STrR _ _ _ -> -1
  Neutral ty _ -> max 0 (uni_level ty - 1)

throw :: (MonadError err m, ?lift_err :: Doc ann -> err) => Doc ann -> m a
throw doc = throwError $ ?lift_err doc

get_name :: Sem m -> Maybe Name  
get_name = \case  
  SPrd _ nm _ _ -> Just nm
  SAbs nm _ _ -> Just nm
  _ -> Nothing

{-------------------------------- MISC INSTANCES -------------------------------}
{-                                                                             -}
{-                                                                             -}
{-                                                                             -}
{-------------------------------------------------------------------------------}


instance Pretty (Sem m) where
  pretty sem = case sem of 
    SUni n -> "𝕌" <> pretty_subscript n
      where
        pretty_subscript =
          pretty . fmap to_subscript . show
        to_subscript c = case c of 
          '0' -> '₀' 
          '1' -> '₁'
          '2' -> '₂'
          '3' -> '₃'
          '4' -> '₄'
          '5' -> '₅'
          '6' -> '₆'
          '7' -> '₇'
          '8' -> '₈'
          '9' -> '₉'
          _ -> c
    SPrd at n a b -> case at of
      Regular -> "(" <> pretty n <+> "⮜" <+> pretty a <> ")" <+> "→" <+> pretty b
      Implicit -> "⟨" <> pretty n <+> "⮜" <+> pretty a <> ")" <+> "→" <+> pretty b
    SAbs n _ _ -> "λ (" <> pretty n <> ")" <+> "..."
    SEql tel ty a b -> "ι" <+> pretty_tel tel <+> pretty ty <+> pretty a <+> pretty b
    SDap tel val -> "ρ" <+> pretty_tel tel <+> pretty val

    SInd nm val ctors ->
      "μ" <+> pretty nm <+> "⮜" <+> pretty val
      <+> nest 2 (vsep (map (\(l,_) -> pretty l <+> "⮜" <+> "...") ctors))
    SCtr label _ vals -> pretty (":" <> label) <+> sep (map pretty vals)
    STrL tel ty val -> "⍃" <+> pretty_tel tel <+> pretty ty <+> pretty val
    STrR tel ty val -> "⍄" <+> pretty_tel tel <+> pretty ty <+> pretty val

    Neutral _ n -> pretty n
    where 
      pretty_tel [(name, (ty, v1, v2), id)] = 
        pretty name <+> "⮜" <+> pretty ty <+> ("(" <> pretty v1 <+> "=" <+> pretty v2 <> ")") <+> "≜" <+> pretty id
      pretty_tel ((name, (ty, v1, v2), id) : tel) = 
        pretty name <+> "⮜" <+> pretty ty <+> ("(" <> pretty v1 <+> "=" <+> pretty v2 <> ")") <+> "≜" <+> pretty id
             <+> "," <+> pretty_tel tel
      pretty_tel [] = "."

instance Pretty (Neutral m) where
  pretty neu = case neu of
    NeuVar n -> pretty n
    NeuApp l r -> pretty l <+> pretty r
    NeuDap _ val -> "ρ …." <+> pretty val
    NeuRec name rty val _ ->
      vsep [ "φ" <+> pretty name <+> "⮜" <+> pretty rty <> "," <+> pretty val <> "."
           , nest 2 "..."
           ] 
        
instance Pretty (Normal m) where
  pretty (Normal _ val) = pretty val

