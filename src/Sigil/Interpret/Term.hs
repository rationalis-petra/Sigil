{-# LANGUAGE ScopedTypeVariables, ImplicitParams #-}
module Sigil.Interpret.Term
  ( Term(..) ) where

import Prelude hiding (head, lookup)
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


data Sem e
  = SUni Integer
  | SPrd Name (Sem e) (Sem e)
  | ISPrd Name (Sem e) (Sem e)
  | SAbs Name InternalCore InternalCore (e (Sem e))
  | ISAbs Name InternalCore InternalCore (e (Sem e))
  | SEql (Sem e) (Sem e) (Sem e)
  | SDap (Sem e)
  | Neutral (Sem e) (Neutral e)

data Neutral e
  = NeuVar Name
  | NeuApp (Neutral e) (Normal e)
  | NeuDap (Neutral e) -- A neutral explicit substitution, must be empty!

data Normal e = Normal (Sem e) (Sem e)


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

read_nf :: forall e err ann m. (MonadError err m, MonadGen m, Environment Name e, ?lift_err :: Doc ann -> err) => Normal e -> m InternalCore
read_nf (Normal ty val) = case (ty, val) of 
  -- Values
  (SPrd name a b, f) -> do
    let neua :: Sem e 
        neua = Neutral a $ NeuVar name
    
        lvl = uni_level a
    a' <- read_nf $ Normal (SUni lvl) a
    f' <- read_nf =<< (Normal <$> (b `app` neua) <*> (f `app` neua))
    pure $ Abs (bind name a') f'
  (SEql ty _ _, SDap val) -> do
    Dap [] <$> read_nf (Normal ty val)

  -- Types
  (SUni k, SEql ty a a') -> do
    Eql [] <$> read_nf (Normal (SUni k) ty)
      <*> read_nf (Normal ty a)
      <*> read_nf (Normal ty a')
  (SUni _, SUni i) -> pure $ Uni i
  (SUni k, SPrd name a b) -> do
    let neua :: Sem e 
        neua = Neutral a $ NeuVar name
    a' <- (read_nf $ Normal (SUni k) a)
    b' <- (read_nf =<< Normal (SUni k) <$> (b `app` neua))
    pure $ Prd (bind name a') b'
        
  (_, Neutral _ e) -> read_ne e 
  (_, _) -> throw ("bad read_nf: " <+> pretty val <> " : " <+> pretty ty)


read_ne :: (MonadError err m, MonadGen m, Environment Name e, ?lift_err :: Doc ann -> err) =>  Neutral e -> m InternalCore
read_ne neu = case neu of 
  NeuVar name -> pure $ Var name
  NeuApp l r -> App <$> (read_ne l) <*> (read_nf r)
  NeuDap val -> Dap [] <$> (read_ne val)

eval :: forall m err e ann. (MonadError err m, MonadGen m, Environment Name e, ?lift_err :: Doc ann -> err) => InternalCore -> e (Sem e) -> m (Sem e)
eval term env = case term of
  Uni n -> pure $ SUni n
  Prd bnd b -> do
    nm <- fromMaybe (throw "Prd must bind a name") (fmap pure $ name bnd)
    a <- fromMaybe (throw "Prd must bind a type") (fmap pure $ tipe bnd)
    a' <- eval a env
    pure $ SPrd nm a' $ SAbs nm a b env
  Var name -> lookup_err ?lift_err name env
  Abs bnd body -> do
    nme <- fromMaybe (throw "Abs must bind a name") (fmap pure $ name bnd)
    a <- fromMaybe (throw "Abs must bind a type") (fmap pure $ tipe bnd)
    pure $ SAbs nme a body env
  App l r -> do
    l' <- (eval l env)
    r' <- (eval r env)
    app l' r'
  Eql tel ty a a' -> do
    if null tel then
      SEql <$> eval ty env  <*> eval a env <*> eval a' env
    else throw "Not sure what to do with Tel in Eql"
    --let eval_tel = 
    
    -- let eval_tel = f
    -- -- TODO: what do we do with tel??
    -- ty' <- (eval ty env)
    -- case ty' of
    --   SUni lvl -> Eql tel' ty' <$> eval a env <*> eval a' env
    --   SPrd nm a b -> do
    --     u <- fresh_name "u"
    --     v <- fresh_name "v"
    --     q <- fresh_name "q"
    --     eql_arg <- eval Eql ?? b (Var u) (Var v)
    --     eql_bdy <- eval Eql ?? b (App a (Var u)) (App a' (Var v))
    --     SPrd u a $ SPrd v b $ SPrd q eql_atg eql_bdy

  Dap tel val -> do
    let eval_tel :: e (Sem e) -> [(AnnBind Name InternalCore, InternalCore)] -> m (e (Sem e))
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
    pure $ ISPrd nm a' $ SAbs nm a b env
  IAbs bnd body -> do
    nme <- fromMaybe (throw "IAbs must bind a name") (fmap pure $ name bnd)
    a <- fromMaybe (throw "IAbs must bind a type") (fmap pure $ tipe bnd)
    pure $ ISAbs nme a body env
  TyCon _ _ -> throw "don't know how to eval tycon"
  --Coreχ _ -> throwError "cannot eval Coreχ terms" 

app :: (MonadError err m, Environment Name e, MonadGen m, ?lift_err :: Doc ann -> err) => (Sem e) -> (Sem e) -> m (Sem e)
app (SAbs name _ body env) val = eval body (insert name val env)
app (Neutral (SPrd _ a b) neu) v =
  Neutral <$> (b `app` v) <*> pure (NeuApp neu (Normal a v))
app l r = throw ("bad args to app:" <+> pretty l <+> "and" <+> pretty r) 

dap :: (MonadError err m, Environment Name e, MonadGen m, ?lift_err :: Doc ann -> err) => e (Sem e) -> (Sem e) -> m (Sem e)
dap _ term = case term of
  Neutral ty neu -> pure $ Neutral (SEql ty (Neutral ty neu) (Neutral ty neu)) (NeuDap neu)
  SAbs name ty body env -> do
    u <- fresh_var "u"
    v <- fresh_var "v"
    id <- fresh_var "id"
    eval (Abs (bind u ty) $
          Abs (bind v ty) $
          Abs (bind id (Eql [] ty (Var u) (Var v))) $
          Dap [(bind name ty, (Var id))] body) env 
  SUni n -> pure $ SDap $ SUni n
  _ -> throw ("don't know how to Dap:" <+> pretty term)

env_eval :: (MonadError err m, MonadGen m, Environment Name e, ?lift_err :: Doc ann -> err) => e (Maybe InternalCore, InternalCore) -> m (e (Sem e))
env_eval = eval_helper eval_var 
  where
    eval_var :: (MonadError err m, MonadGen m, Environment Name e, ?lift_err :: Doc ann -> err) =>
                Name -> (Maybe InternalCore, InternalCore) -> e (Sem e) -> m (Sem e)
    eval_var n (Nothing, ty) env = mkvar n ty env
    eval_var _ (Just val, _) env = eval val env
    
    mkvar :: (MonadError err m, MonadGen m, Environment Name e, ?lift_err :: Doc ann -> err) =>
              Name -> InternalCore -> e (Sem e) -> m (Sem e)
    mkvar n ty env = do
      ty' <- eval ty env
      pure $ Neutral ty' (NeuVar n)
  
-- TODO: fix this function - it is wrong!
uni_level :: Sem e -> Integer
uni_level sem = case sem of 
  SUni n -> n + 1
  SPrd _ l r -> max (uni_level l) (uni_level r)
  SAbs _ _ _ _ -> 0 -- note: predicative vs impredicative!!
  SEql ty _ _ -> uni_level ty
  SDap val -> uni_level val

  ISPrd _ l r -> max (uni_level l) (uni_level r)
  ISAbs _ _ _ _ -> 0 -- note: predicative vs impredicative!!
  Neutral _ _ -> 0 -- TODO: this is probably wrong!!!

throw :: (MonadError err m, ?lift_err :: Doc ann -> err) => Doc ann -> m a
throw doc = throwError $ ?lift_err doc

{-------------------------------- MISC INSTANCES -------------------------------}
{-                                                                             -}
{-                                                                             -}
{-                                                                             -}
{-------------------------------------------------------------------------------}


instance Pretty (Sem e) where
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
    SAbs n _ body _ -> "λ (" <> pretty n <> ")" <+> pretty body
    SEql ty a b -> "ι." <+> pretty ty <+> pretty a <+> pretty b
    SDap val -> "ρ." <+> pretty val
    Neutral _ n -> pretty n
  
    ISPrd n a b -> "{" <> pretty n <+> ":" <+> pretty a <> "}" <+> "→" <+> pretty b
    ISAbs n _ body _ -> "λ {" <> pretty n <> "}" <+> pretty body

instance Pretty (Neutral e) where
  pretty neu = case neu of
    NeuVar n -> pretty n
    NeuApp l r -> pretty l <+> pretty r
    NeuDap val -> "Ap" <+> pretty val

instance Pretty (Normal e) where
  pretty (Normal _ val) = pretty val

