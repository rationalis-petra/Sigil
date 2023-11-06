{-# LANGUAGE ScopedTypeVariables, ImplicitParams #-}
module Sigil.Interpret.Term
  ( Term(..) ) where

import Prelude hiding (head, lookup)
import Data.Kind
import Data.Maybe
import Control.Monad.Except (MonadError, throwError)

import Prettyprinter

import Sigil.Abstract.Environment
import Sigil.Abstract.AlphaEq
import Sigil.Concrete.Internal
  

{------------------------------ THE TERM CLASSES -------------------------------}
{- The Term class supports only two methods:                                   -}
{- • normalize: convert to canonical (Β-normal, η-long) form                   -}
{- • equiv: αβη equivalence                                                    -}
{-                                                                             -}
{- Both accept an environment. Currently, this is a local environment, but     -}
{- eventually the environment will also include a 'global' (i.e. surrounding   -}
{- module) component as well, to look up qualified names (QName)               -}
{-                                                                             -}
{- There is also the TermDec class, which must be fulfilled by any Decorations -}
{- used on the Term Syntax tree.                                               -}
{-                                                                             -}
{-------------------------------------------------------------------------------}


class Term a where
  normalize :: (MonadError err m, MonadGen m, Environment Name e) => (Doc ann -> err) -> e (Maybe a,a) -> a -> a -> m a
  equiv :: (MonadError err m, MonadGen m, Environment Name e) => (Doc ann -> err) -> e (Maybe a,a) -> a -> a -> a -> m Bool


{------------------------------ DENOTATIVE TERMS -------------------------------}
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


 

data Sem m e
  = SUni Integer
  | SPrd Name (Sem m e) (Sem m e)
  | ISPrd Name (Sem m e) (Sem m e)
  | SAbs Name (Sem m e -> m (Sem m e))
  | ISAbs Name (Sem m e -> m (Sem m e))
  | SEql [(Name, (Sem m e, Sem m e, Sem m e), Sem m e)] (Sem m e) (Sem m e) (Sem m e)
  | SDap (Sem m e)
  | Neutral (Sem m e) (Neutral m e)

data Neutral m e
  = NeuVar Name
  | NeuApp (Neutral m e) (Normal m e)
  | NeuDap (Neutral m e) -- A neutral explicit substitution, must be empty!

data Normal (m :: Type -> Type) (e :: Type -> Type) = Normal (Sem m e) (Sem m e)


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


-- TODO: now we use IDs for names, need to ensure we do capture-avoiding substitution!!
instance Term InternalCore where
  normalize lift_error env ty term =
    let ?lift_err = lift_error in
      let ty' = eval ty =<< env_eval env
          term' = eval term =<< env_eval env
      in read_nf =<< (Normal <$> ty' <*> term')


  equiv lift_error env ty x y = (αeq) <$> normalize lift_error env ty x <*> normalize lift_error env ty y
    where 
      ?lift_err = lift_error

read_nf :: forall e err ann m. (MonadError err m, MonadGen m, Environment Name e, ?lift_err :: Doc ann -> err) => Normal m e -> m InternalCore
read_nf (Normal ty val) = case (ty, val) of 
  -- Values
  (SPrd name a b, f) -> do
    let neua :: Sem m e 
        neua = Neutral a $ NeuVar name
    
        lvl = uni_level a
    a' <- read_nf $ Normal (SUni lvl) a
    f' <- read_nf =<< (Normal <$> (b `app` neua) <*> (f `app` neua))
    pure $ Abs (bind name a') f'
  -- TODO: figure out what to do with SEql telescope?!
  -- possibly it is guaranteed to be empty, as SDap is a telescope??
  (SEql [] ty _ _, SDap val) -> do
    Dap [] <$> read_nf (Normal ty val)

  -- Types
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
  (SUni _, SUni i) -> pure $ Uni i
  (SUni k, SPrd name a b) -> do
    let neua :: Sem m e 
        neua = Neutral a $ NeuVar name
    a' <- (read_nf $ Normal (SUni k) a)
    b' <- (read_nf =<< Normal (SUni k) <$> (b `app` neua))
    pure $ Prd (bind name a') b'
        
  (_, Neutral _ e) -> read_ne e 
  (_, _) -> throw ("bad read_nf: " <+> pretty val <> " : " <+> pretty ty)


read_ne :: (MonadError err m, MonadGen m, Environment Name e, ?lift_err :: Doc ann -> err) =>  Neutral m e -> m InternalCore
read_ne neu = case neu of 
  NeuVar name -> pure $ Var name
  NeuApp l r -> App <$> (read_ne l) <*> (read_nf r)
  NeuDap val -> Dap [] <$> (read_ne val)

eval :: forall m err e ann. (MonadError err m, MonadGen m, Environment Name e, ?lift_err :: Doc ann -> err) => InternalCore -> e (Sem m e) -> m (Sem m e)
eval term env = case term of
  Uni n -> pure $ SUni n
  Prd bnd b -> do
    nm <- fromMaybe (throw "Prd must bind a name") (fmap pure $ name bnd)
    a <- fromMaybe (throw "Prd must bind a type") (fmap pure $ tipe bnd)
    a' <- eval a env
    pure $ SPrd nm a' $ SAbs nm (\val -> eval b (insert nm val env))
  Var name -> lookup_err ?lift_err name env
  Abs bnd body -> do
    nme <- fromMaybe (throw "Abs must bind a name") (fmap pure $ name bnd)
    pure $ SAbs nme (\val -> eval body (insert nme val env))
  App l r -> do
    l' <- (eval l env)
    r' <- (eval r env)
    app l' r'
  Eql tel ty v1 v2 -> do
    -- Eql evaluation is divided into three phases:
    -- Phase 1: eliminate all instances of ρ (refl) from the telescope
    -- Phase 2: perform all ty eliminations
    -- Phase 3: eliminate unused bindings

    
    -- Extract reflections
    -- TODO: eliminate unused binds
    let eval_tel :: [(AnnBind Name (InternalCore, InternalCore, InternalCore), InternalCore)] -> e (Sem m e)
          -> m ([(Name, (Sem m e, Sem m e, Sem m e), Sem m e)], e (Sem m e))
        eval_tel [] env = pure ([], env)
        eval_tel ((bnd, id) : tel) env = do 
          name <- fromMaybe (throw "Eql Telescope must bind a name") (fmap pure $ name bnd)
          id' <- eval id env 
          case id' of 
            SDap val -> 
              eval_tel tel (insert name val env)
            _ -> do
              (ty, v1, v2) <- fromMaybe (throw "Eql Telescope must bind an equality") (fmap pure $ tipe bnd)
              ty' <- eval ty env 
              v1' <- eval v1 env 
              v2' <- eval v2 env 
    -- TODO: inserting neutral terms into environment may be bad!!
              (tel', env') <- eval_tel tel (insert name (Neutral ty' (NeuVar name)) env)
              pure $ ((name, (ty', v1', v2'), id') : tel', env')

    (tel_sem, env') <- eval_tel tel env
    ty_sem <- eval ty env  
    eql env' tel_sem ty_sem v1 v2
    -- TODO: phase 3!!
    -- pure $ SEql tel' ty' v1' v2'

  Dap tel val -> do
    let eval_tel :: e (Sem m e) -> [(AnnBind Name (InternalCore, InternalCore, InternalCore), InternalCore)] -> m (e (Sem m e))
        eval_tel env [] = pure env
        eval_tel env ((bind, val) : tel) = do 
          name <- fromMaybe (throw "Ap Telescope must bind a name") (fmap pure $ name bind)
          val' <- eval val env 
          eval_tel (insert name val' env) tel
    env' <- eval_tel env tel
    val' <- eval val env'
    dap env val' 

  -- Implicit terms 
  IPrd bnd b -> do
    nm <- fromMaybe (throw "Prd must bind a name") (fmap pure $ name bnd)
    a <- fromMaybe (throw "Prd must bind a type") (fmap pure $ tipe bnd)
    a' <- eval a env
    pure $ ISPrd nm a' $ SAbs nm (\val -> eval b (insert nm val env))
  IAbs bnd body -> do
    nme <- fromMaybe (throw "IAbs must bind a name") (fmap pure $ name bnd)
    pure $ ISAbs nme (\val -> eval body (insert nme val env))
  TyCon _ _ -> throw "don't know how to eval tycon"
  --Coreχ _ -> throwError "cannot eval Coreχ terms" 

app :: (MonadError err m, Environment Name e, MonadGen m, ?lift_err :: Doc ann -> err) => (Sem m e) -> (Sem m e) -> m (Sem m e)
app (SAbs _ fnc) val = fnc val
app (Neutral (SPrd _ a b) neu) v =
  Neutral <$> (b `app` v) <*> pure (NeuApp neu (Normal a v))
app l r = throw ("bad args to app:" <+> pretty l <+> "and" <+> pretty r) 

dap :: (MonadError err m, Environment Name e, MonadGen m, ?lift_err :: Doc ann -> err) => e (Sem m e) -> (Sem m e) -> m (Sem m e)
dap env term = case term of
  Neutral ty neu -> pure $ Neutral (SEql [] ty (Neutral ty neu) (Neutral ty neu)) (NeuDap neu)
  SAbs _ fnc -> do
    u <- fresh_var "u"
    v <- fresh_var "v"
    id <- fresh_var "id"
    pure (SAbs u
          (\uval ->
             pure $ SAbs v
             (\vval -> 
                pure $ SAbs id
                (\idval -> do
                   res <- fnc idval
                   dap (insert id idval . insert v vval . insert u uval $ env) res))))
  SUni n -> pure $ SDap $ SUni n
  _ -> throw ("Don't know how to dap:" <+> pretty term)

eql :: (MonadError err m, Environment Name e, MonadGen m, ?lift_err :: Doc ann -> err) => e (Sem m e) -> [(Name, (Sem m e, Sem m e, Sem m e), Sem m e)] -> (Sem m e)
  -> InternalCore -> InternalCore -> m (Sem m e)
eql env tel tipe v1 v2 = case tipe of
  Neutral _ _ -> SEql tel tipe <$> eval v1 env <*> eval v2 env -- TODO: is this neutral??
  SPrd name a fnc -> do
    u <- fresh_var "u"
    v <- fresh_var "v"
    id <- fresh_var "id"
    pure (SPrd u a $ SAbs u
           (\uval ->
             pure $ SPrd v a $ SAbs v 
             (\vval ->
               pure $ SPrd id (SEql tel a uval vval) $ SAbs id
               (\idval -> do
                   b <- fnc `app` idval -- TODO: I think this is wrong?~
                   eql (insert u uval . insert v vval . insert id idval $ env)
                    (tel <> [(name, (a, uval, vval), idval)])
                    b (App v1 (Var u)) (App v2 (Var v))))))
  SUni n -> SEql tel (SUni n) <$> eval v1 env <*> eval v2 env
  _ -> throw ("Don't know how to eql:" <+> pretty tipe)

env_eval :: (MonadError err m, MonadGen m, Environment Name e, ?lift_err :: Doc ann -> err) => e (Maybe InternalCore, InternalCore) -> m (e (Sem m e))
env_eval = eval_helper eval_var 
  where
    eval_var :: (MonadError err m, MonadGen m, Environment Name e, ?lift_err :: Doc ann -> err) =>
                Name -> (Maybe InternalCore, InternalCore) -> e (Sem m e) -> m (Sem m e)
    eval_var n (Nothing, ty) env = mkvar n ty env
    eval_var _ (Just val, _) env = eval val env
    
    mkvar :: (MonadError err m, MonadGen m, Environment Name e, ?lift_err :: Doc ann -> err) =>
              Name -> InternalCore -> e (Sem m e) -> m (Sem m e)
    mkvar n ty env = do
      ty' <- eval ty env
      pure $ Neutral ty' (NeuVar n)
  
-- TODO: fix this function - it is wrong!
uni_level :: Sem m e -> Integer
uni_level sem = case sem of 
  SUni n -> n + 1
  SPrd _ l r -> max (uni_level l) (uni_level r)
  SAbs _ _ -> 0 -- note: predicative vs impredicative!!
  SEql _ ty _ _ -> uni_level ty
  SDap val -> uni_level val

  ISPrd _ l r -> max (uni_level l) (uni_level r)
  ISAbs _ _ -> 0 -- note: predicative vs impredicative!!
  Neutral _ _ -> 0 -- TODO: this is probably wrong!!!

throw :: (MonadError err m, ?lift_err :: Doc ann -> err) => Doc ann -> m a
throw doc = throwError $ ?lift_err doc

{-------------------------------- MISC INSTANCES -------------------------------}
{-                                                                             -}
{-                                                                             -}
{-                                                                             -}
{-------------------------------------------------------------------------------}


instance Pretty (Sem m e) where
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
    SPrd n a b -> pretty n <> " : " <> pretty a <+> "→" <+> pretty b
    SAbs n _ -> "λ (" <> pretty n <> ")" <+> "..."
    SEql tel ty a b -> "ι" <+> pretty_tel tel <+> "." <+> pretty ty <+> pretty a <+> pretty b
      where 
        pretty_tel [(name, (ty, v1, v2), id)] = 
          pretty name <+> "⮜" <+> pretty ty <+> ("(" <> pretty v1 <+> "=" <+> pretty v2 <> ")") <+> "≜" <+> pretty id
        pretty_tel ((name, (ty, v1, v2), id) : tel) = 
          pretty name <+> "⮜" <+> pretty ty <+> ("(" <> pretty v1 <+> "=" <+> pretty v2 <> ")") <+> "≜" <+> pretty id
               <+> "," <+> pretty_tel tel
        pretty_tel [] = ""
    SDap val -> "ρ." <+> pretty val
    Neutral _ n -> pretty n
  
    ISPrd n a b -> "{" <> pretty n <+> ":" <+> pretty a <> "}" <+> "→" <+> pretty b
    ISAbs n _ -> "λ {" <> pretty n <> "}" <+> "..."

instance Pretty (Neutral m e) where
  pretty neu = case neu of
    NeuVar n -> pretty n
    NeuApp l r -> pretty l <+> pretty r
    NeuDap val -> "Ap" <+> pretty val

instance Pretty (Normal m e) where
  pretty (Normal _ val) = pretty val

