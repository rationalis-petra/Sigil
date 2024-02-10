{-# LANGUAGE ScopedTypeVariables, ImplicitParams #-}
module Sigil.Interpret.Canonical.Term
  ( Term(..)
  , eval
  , eval_module
  , eval_package
  ) where


import Prelude hiding (head, lookup)
import Control.Monad((<=<))
import Control.Monad.Except (MonadError, throwError)
import Control.Lens(view, (^.), _1, _2, _3)

import qualified Data.Map as Map
import qualified Data.List.NonEmpty as NonEmpty
import qualified Data.Set as Set
import Data.Set (Set)
import Data.List.NonEmpty (NonEmpty(..))
import Data.Maybe
import Data.Text (Text)
import Data.Foldable (find)

import Prettyprinter
import Topograph

import Sigil.Abstract.Names
import Sigil.Abstract.Syntax (Entry(..), MTree(..)
                             , module_header, module_entries, module_exports, module_imports
                             , package_modules, package_header, package_name, provides, requires
                             , ImportDef(..) )
import Sigil.Abstract.Environment (insert_at_path, get_modulo_path)
import Sigil.Abstract.AlphaEq
import Sigil.Concrete.Decorations.Implicit
import Sigil.Concrete.Internal
import Sigil.Interpret.Canonical.Values
  

{------------------------------ THE TERM CLASSES -------------------------------}
{- The Term represents types which can be normalized/evaluated. As such, it    -}
{- supports two primary methods:                                               -}
{- • normalize: convert to canonical (Β-normal, η-long) form                   -}
{- • equiv: αβη equivalence                                                    -}
{-------------------------------------------------------------------------------}


class Term a where
  normalize :: (MonadError err m, MonadGen m) => (Doc ann -> err) -> SemEnv m -> a -> a -> m a
  equiv :: (MonadError err m, MonadGen m) => (Doc ann -> err) -> SemEnv m -> a -> a -> a -> m Bool


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
{-------------------------------------------------------------------------------}

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
      let ty' = eval ty env
          term' = eval term env
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
      neua = Neutral a $ NeuVar name
      lvl = uni_level a

    a' <- read_nf $ Normal (SUni lvl) a
    f' <- read_nf =<< (Normal <$> (app at b neua) <*> (app at f neua))
    pure $ Abs at (bind name a') f'

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
    b' <- (read_nf =<< Normal (SUni k) <$> (app at b neua))
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
        recur (Ctr label ind_ty) cty' vals
        where
          recur v _ [] = pure v
          recur v (SPrd at _ a b) (val:vals) = do
            b' <- app at b val
            val' <- read_nf (Normal a val)
            recur (App at v val') b' vals
          recur _ _ _ = throw "recur unequal!"
      Nothing -> throw $ "Constructor" <+> pretty label <+> "cannot be found in type" <+> pretty (SInd nm ty ctors)
        
  (_, Neutral _ e) -> read_ne e 
  (_, _) -> throw ("bad read_nf:" <+> pretty val <+> "⮜" <+> pretty ty)


read_ne :: (MonadError err m, MonadGen m, ?lift_err :: Doc ann -> err) => Neutral m -> m InternalCore
read_ne neu = case neu of 
  NeuVar name -> pure $ Var name
  NeuApp at l r -> App at <$> (read_ne l) <*> (read_nf r)
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
    (at, a, b) <- case ty of
      SPrd at _ a b -> pure (at, a, b)
      _ -> throw "bad read_ne in recursive"
    b' <- app at b a
    val'<- read_ne val
    let read_case (_, m) = do
          (ptn, core) <- m
          core' <- read_nf (Normal b' core)
          pure $ (ptn, core')
    cases' <- mapM read_case cases
    pure $ Rec (AnnBind (nm, ty')) val' cases'

eval_package :: forall m err ann. (MonadError err m, MonadGen m, ?lift_err :: Doc ann -> err) => SemEnv m -> InternalPackage -> m (SemPackage m)
eval_package env package = do

  -- dependencies :: MTree -> Map (NonEmpty Text) (Set (NonEmpty Text))
  let dependencies (MTree mt) = Map.foldrWithKey (go []) Map.empty mt where
        go psf name (m_mod, m_tree) out =
          let out' = case m_mod of 
                Just modul -> Map.insert (NonEmpty.reverse $ name :| psf) (mod_deps modul) out 
                Nothing -> out
          in case m_tree of
            Just (MTree mt) -> Map.foldrWithKey (go (name : psf)) out' mt
            Nothing -> out'


      mod_deps :: InternalModule -> Set (NonEmpty Text)
      mod_deps = Set.fromList . filter (flip Set.member pkg_mnames) .  fmap im_deps . (view module_imports)
      im_deps (Im (p,_)) = p -- TODO: this is definitely wrong!

      -- The set of available modules (internal) whose paths are available 
      pkg_mnames :: Set (NonEmpty Text)
      pkg_mnames = go1 (package^.package_modules) Set.empty where
        go1 (MTree mt) out =
          Map.foldrWithKey (go2 []) out mt

        go2 :: [Text] -> Text -> (Maybe InternalModule, Maybe (MTree InternalModule)) -> Set (NonEmpty Text) -> Set (NonEmpty Text)
        go2 psf k (mm, mt) out =
          let out' = maybe out (const $ Set.insert (NonEmpty.reverse (k :| psf)) out) mm
          in case mt of 
            Just (MTree subtree) -> Map.foldrWithKey (go2 (k:psf)) out' subtree 
            Nothing -> out'

   
  let eval_package_modules :: [NonEmpty Text] -> m (MTree (SemModule m))
      eval_package_modules mdle_names = foldl coll (pure (MTree Map.empty)) =<< get_modules mdle_names

      get_modules :: [NonEmpty Text] -> m [InternalModule]
      get_modules [] = pure []
      get_modules (p : ps) = case get_modulo_path p (package^.package_modules) of 
        Just (m, []) -> (m :) <$> get_modules ps
        Just _ -> throw "Modulo path; can't deal"
        Nothing -> throw "Lost module in get_modules in eval_package"


      coll :: m (MTree (SemModule m)) -> InternalModule -> m (MTree (SemModule m))
      coll comp_mtree modul = do
        mtree <- comp_mtree
        smodule <- eval_module ( view _1 env
                               , view _2 env
                               , Map.insert (package^.package_header.package_name)
                                 (SemPackage (package^.package_header.requires) (package^.package_header.provides) mtree)
                                 (view _3 env) ) modul 
        pure $ (insert_at_path (snd . unPath $ (modul^.module_header)) smodule mtree)
      

  -- Step 1: topological sort dependencies
  modules' <- case runG (dependencies (package^.package_modules))
                        (\g -> eval_package_modules $ fmap (gFromVertex g) $ gVertices g) of 
    Left _ -> throw "Cyclic dependencies found in package"
    Right m -> m
    
  pure $ SemPackage (package^.package_header.requires) (package^.package_header.provides) modules'
  

eval_module :: forall m err ann. (MonadError err m, MonadGen m, ?lift_err :: Doc ann -> err) => SemEnv m -> InternalModule -> m (SemModule m)
eval_module env modul = 
  let go env (Singleχ _ (AnnBind (Name n, _)) val : es) = do
        val' <- eval val env
        case n of
          Left qn -> ((name_text (Name n), val') :) <$> go (insert_path qn val' env) es
          Right _ -> throw "Internal error: Bad name bind in eval_module"
      go _ [] = pure []
  in SemModule (modul^.module_imports) (modul^.module_exports)
      <$> go env (modul^.module_entries)

eval :: forall m err ann. (MonadError err m, MonadGen m, ?lift_err :: Doc ann -> err) => InternalCore -> SemEnv m -> m (Sem m)
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
  App at l r -> do
    l' <- (eval l env)
    r' <- (eval r env)
    app at l' r'

  Ind inm ity ctors -> do 
    ity' <- eval ity env
    -- let env' = 
    let ctors' = fmap (\(lbl, a) ->
                       (lbl, (\val -> eval a (insert inm val env))))
                ctors
    pure $ SInd inm ity' ctors'

  Ctr label ty -> SCtr label <$> (eval ty env) <*> pure []

  -- Evaluate a recursive pattern-matching term
  -- We use the recur helper funtion, which requires that each 
  -- pattern-match case be expressed as a function which:
  -- • Takes a value to match and returns either
  --   • Nothing (if the match failed)
  --   • Just val (if the match succeeded, where val is the evaluated case)

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

        -- Responsible for producinga match
        match :: SemEnv m -> Pattern Name -> Sem m -> Maybe (SemEnv m)
        match env (PatVar n) v = Just $ insert n v env
        match env (PatCtr n subpats) (SCtr n' _ vals)
          | n == n' = foldr (\(p, v) menv -> do -- TODO: check that foldl is correct!
                                env <- menv
                                match env p v) (Just env) (zip subpats vals)
          | otherwise = Nothing
        match _ _ _ = Nothing

        match_neu :: SemEnv m -> Pattern Name -> Sem m -> m (SemEnv m)
        match_neu env (PatVar n) ty = pure $ insert n (Neutral ty (NeuVar n)) env
        match_neu env (PatCtr label subpats) (SInd _ _ ctors) = do
          -- args <- ty_args label ctors
          let ty_args :: Sem m -> m [Sem m]
              ty_args = \case -- TODO: borked! include name!
                (SPrd at n a b) -> (a :) <$> (ty_args =<< (app at b (Neutral a (NeuVar n))))
                _ -> pure []
          args <- case find ((== label) . fst) ctors of
            Just (_, ty) -> ty_args =<< ty (Neutral rty' (NeuVar rname))
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
    v1_sem <- eval v1 env'
    v2_sem <- eval v2 env'
    eql env' tel_sem ty_sem v1_sem v2_sem
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
    eval_over env' (\tel -> if null tel then (\_ v -> v) else STrL tel) tel' ty' val'
  TrR tel ty val -> do
    (tel', env') <- eval_tel env tel
    ty' <- eval ty env'
    val' <- eval val env'
    eval_over env' (\tel -> if null tel then (\_ v -> v) else STrR tel) tel' ty' val'
  -- LfL tel ty val -> eval_over env LfL tel ty val
  -- LfR tel ty val -> eval_over env LfR tel ty val
  -- Implicit terms 

{-------------------------------------------------------------------------------}
{-                                                                             -}
{-------------------------------------------------------------------------------}

eval_over :: forall m err ann. (MonadError err m, MonadGen m, ?lift_err :: Doc ann -> err)
  => (SemEnv m) -> (SemTel m -> Sem m -> Sem m -> Sem m)
    -> SemTel m -> Sem m -> Sem m -> m (Sem m) 
eval_over env ctor tel ty val = do
  -- reduce over type families
  case ty of 
    SPrd at name a fnc -> do
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
                     ty' <- app at fnc (Neutral a (NeuVar name))
                     val' <- app at val (Neutral a (NeuVar name))
                     eval_over (insert id idval . insert v vval . insert u uval $ env)
                       ctor (tel <> [(name, (a, uval, vval), idval)])
                       ty' val'))))
    SUni _ -> pure $ ctor tel ty val
    SInd _ _ _ ->
      throw ("Don't know how to reduce over type:" <+> pretty ty)
    _ -> throw ("over expects a type as first value, got:" <+> pretty ty)

eval_tel :: forall m err ann. (MonadError err m, MonadGen m, ?lift_err :: Doc ann -> err)
  => (SemEnv m) -> [(AnnBind Name (InternalCore, InternalCore, InternalCore), InternalCore)]
    -> m ([(Name, (Sem m, Sem m, Sem m), Sem m)], SemEnv m)
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
  => (SemEnv m) -> SemTel m -> m (SemTel m, SemEnv m)
eval_stel env tel = go env tel [] where 
  go :: (SemEnv m) -> SemTel m -> SemTel m -> m (SemTel m, SemEnv m)
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

eval_sem :: forall m err ann. (MonadError err m, MonadGen m, ?lift_err :: Doc ann -> err) => (SemEnv m) -> (Sem m) -> m (Sem m)
eval_sem env term = case term of
  SUni n -> pure $ SUni n
  SPrd at n a b -> do
    a' <- eval_sem env a
    pure $ SPrd at n a' $ SAbs n a' (eval_sem env <=< app at b)
  SAbs n a f -> do
    a' <- eval_sem env a
    pure $ SAbs n a' (eval_sem env <=< f)
  SEql tel ty v1 v2 -> do
    (tel_sem, env') <- eval_stel env tel 
    ty_sem <- eval_sem env ty   
    eql env' tel_sem ty_sem v1 v2
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


eval_neusem :: forall m err ann. (MonadError err m, MonadGen m, ?lift_err :: Doc ann -> err) => (SemEnv m) -> (Neutral m) -> m (Sem m)
eval_neusem env neu = case neu of 
  NeuVar n -> lookup_err ?lift_err n env
  NeuApp at l (Normal _ r) -> do
    l' <- eval_neusem env l
    r' <- eval_sem env r
    app at l' r'
  -- TODO: eval_neutel
  NeuDap tel v -> dap env tel =<< eval_neusem env v
  NeuRec name ty neu cases -> do 
    ty' <- eval_sem env ty
    neu' <- eval_neusem env neu
    recur env name ty' neu' cases -- TODO: cases'
      

app :: (MonadError err m, MonadGen m, ?lift_err :: Doc ann -> err) => ArgType -> (Sem m) -> (Sem m) -> m (Sem m)
app _ (SAbs _ _ fnc) val = fnc val
app _ (SCtr label ty vals) v =
  pure $ SCtr label ty (vals <> [v])
app _ (Neutral (SPrd at _ a b) neu) v =
  Neutral <$> (app at b v) <*> pure (NeuApp at neu (Normal a v))
app _ l r = throw ("bad args to app:" <+> pretty l <+> "and" <+> pretty r) 

dap :: (MonadError err m, MonadGen m, ?lift_err :: Doc ann -> err) => (SemEnv m) -> SemTel m -> (Sem m) -> m (Sem m)
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


recur :: (MonadError err m, MonadGen m, ?lift_err :: Doc ann -> err)
  => (SemEnv m) -> Name -> Sem m -> Sem m -> [(Sem m -> Maybe (m (Sem m)), m (Pattern Name, Sem m))] -> m (Sem m)
recur _ rname rty@(SPrd at _ a b) val cases =
    case val of 
      SCtr _ _ _ -> case find (isJust) (map (($ val) . fst) cases) of 
        Just (Just m) -> m
        _ -> throw ("Failed to match val:" <+> pretty val <+> "at type" <+> pretty a)
      Neutral _ neuval -> 
        Neutral <$> (app at b val) <*> pure (NeuRec rname rty neuval cases)
      _ -> throw "recur must induct over a constructor"
recur _ _ _ _ _ = throw "recur expects recursive type to be fn" 

eql :: (MonadError err m, MonadGen m, ?lift_err :: Doc ann -> err) => (SemEnv m) -> [(Name, (Sem m, Sem m, Sem m), Sem m)] -> Sem m
  -> Sem m -> Sem m -> m (Sem m)
eql env tel tipe v1 v2 = case tipe of
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
               eqty <- (eql (insert u uval . insert v vval $ env) tel a uval vval)
               pure $ SPrd at id eqty (SAbs id eqty
                 (\idval -> do
                     b <- app at fnc (Neutral a (NeuVar name)) -- TODO: I think this is wrong?
                     v1' <- app at v1 uval
                     v2' <- app at v2 vval 
                     eql (insert u uval . insert v vval . insert id idval . insert name (Neutral a (NeuVar name)) $ env)
                      (tel <> [(name, (a, uval, vval), idval)])
                      b v1' v2')))))
  SUni n -> SEql tel (SUni n) <$> eval_sem env v1 <*> eval_sem env v2
  SInd _ _ _  -> throw ("Don't know how to reduce ι at type:" <+> pretty tipe)
  _ -> throw ("ι must reduce on type, got:" <+> pretty tipe)
  
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

    
  

  


