{-# LANGUAGE ScopedTypeVariables #-}
module Glyph.Interpret.Term
  ( Term(..) ) where

import Prelude hiding (head, lookup)
import Data.Maybe
import Control.Monad.Except (MonadError, throwError)

import Prettyprinter

import Glyph.Abstract.Syntax
import Glyph.Abstract.Environment
import Glyph.Abstract.AlphaEq
  

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


class Pretty a => Term a where
  normalize :: (MonadError (Doc ann) m, Environment Name e) => e (Maybe a,a) -> a -> a -> m a
  equiv :: (MonadError (Doc ann) m, Environment Name e) => e (Maybe a,a) -> a -> a -> a -> m Bool

-- class (Default χ, DecEq χ, DecPretty χ) => TermDec χ where  
--(Eq (Core AnnBind Name χ), Pretty (Core AnnBind Name χ))
--(Pretty (Core AnnBind Name χ), MonadError (Doc ann) m, Environment Name e)
--(Pretty (Core AnnBind Name χ), MonadError (Doc ann) m, Environment Name e)

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


data Sem e b χ
  = SUni (Uniχ χ) Int
  | SPrd (Prdχ χ) Name (Sem e b χ) (Sem e b χ)
  | SAbs Name (Core b Name χ) (e (Sem e b χ))
  | Neutral (Sem e b χ) (Neutral e b χ)

data Neutral e b χ
  = NeuVar (Varχ χ) Name
  | NeuApp (Appχ χ) (Neutral e b χ) (Normal e b χ)

data Normal e b χ = Normal (Sem e b χ) (Sem e b χ)


{-------------------------------- TERM INSTANCE --------------------------------}
{- The term instance for Core applies type directed normalization by           -}
{- evaluation. Equality is derived from the Eq instance defined in Core.hs,    -}
{- extended to first perform normalization.                                    -}
{-                                                                             -}
{- Normalization relies on a few key helper functions:                         -}
{- • eval performs untyped evaluation, converting any term into a Semantic     -}
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
instance (AlphaEq Name (Core AnnBind Name χ), Pretty (Core AnnBind Name χ), Forallχ Monoid χ) => Term (Core AnnBind Name χ) where
  normalize env ty term =
    read_nf =<< (Normal <$> ty' <*> term')
    where
      ty' = eval ty =<< env_eval env
      term' = eval term =<< env_eval env

  equiv env ty x y = (αeq) <$> normalize env ty x <*> normalize env ty y


read_nf :: forall e χ m b ann. (Binding b, Pretty (Core b Name χ), Forallχ Monoid χ, MonadError (Doc ann) m, Environment Name e) =>
  Normal e b χ -> m (Core b Name χ)
read_nf (Normal ty val) = case (ty, val) of 
  (SPrd _ name a b, f) -> do
    let neua :: Sem e b χ 
        neua = Neutral a $ NeuVar mempty name
    
        lvl = uni_level a
    a' <- read_nf $ Normal (SUni mempty lvl) a
    f' <- read_nf =<< (Normal <$> (b `app'` neua) <*> (f `app'` neua))
    -- TODO: we can probably derive the χ-decoration from f somehow...
    pure $ Abs mempty (bind name a') f'
  (SUni _ _, SUni χ i) -> pure $ Uni χ i
  (SUni χ₁ k, SPrd χ₂ name a b) -> do
    a' <- (read_nf $ Normal (SUni χ₁ k) a)
    b' <- (read_nf $ Normal (SPrd χ₂ name a (SUni mempty k)) b)
    pure $ Prd χ₂ (bind name a') b'
        
  (_, Neutral _ e) -> read_ne e 
  (_, _) -> throwError ("bad read_nf: " <+> pretty val <> " : " <+> pretty ty)

read_ne :: (Binding b, Pretty (Core b Name χ), Forallχ Monoid χ, MonadError (Doc ann) m, Environment Name e) =>
             Neutral e b χ -> m (Core b Name χ)
read_ne neu = case neu of 
  NeuVar χ name -> pure $ Var χ name
  NeuApp χ l r -> App χ <$> (read_ne l) <*> (read_nf r)

eval :: (Binding b, Pretty (Core b Name χ), Forallχ Monoid χ, MonadError (Doc ann) m, Environment Name e) =>
          Core b Name χ -> e (Sem e b χ) -> m (Sem e b χ)
eval term env = case term of
  Coreχ _ -> throwError "cannot eval Coreχ terms" 
  Uni χ n -> pure $ SUni χ n
  Prd χ bnd b -> do
    nm <- fromMaybe (throwError "Prd must bind a name") (fmap pure $ name bnd)
    a <- fromMaybe (throwError "Prd must bind a type") (fmap pure $ tipe bnd)
    a' <- eval a env
    pure $ SPrd χ nm a' $ SAbs nm b env
  Var _ name -> lookup_err name env
  Abs _ bnd body -> do
    nme <- fromMaybe (throwError "Abs must bind a name") (fmap pure $ name bnd)
    pure $ SAbs nme body env
  App χ l r -> do
    l' <- (eval l env)
    r' <- (eval r env)
    app χ l' r'

app' :: (Binding b, Pretty (Core b Name χ), Forallχ Monoid χ, MonadError (Doc ann) m, Environment Name e) =>
          Sem e b χ -> Sem e b χ -> m (Sem e b χ)
app' = app mempty

app :: (Binding b, Pretty (Core b Name χ), Forallχ Monoid χ, MonadError (Doc ann) m, Environment Name e) =>
         Appχ χ -> Sem e b χ -> Sem e b χ -> m (Sem e b χ)
app _ (SAbs name body env) val = eval body (insert name val env)
app χ (Neutral (SPrd _ _ a b) neu) v =
  Neutral <$> (b `app'` v) <*> pure (NeuApp χ neu (Normal a v))
app _ _ _ = throwError "bad args to app"

env_eval :: (Binding b, Pretty (Core b Name χ), Forallχ Monoid χ, MonadError (Doc ann) m, Environment Name e) =>
              e (Maybe (Core b Name χ), Core b Name χ) -> m (e (Sem e b χ))
env_eval = eval_helper eval_var 
  where

    
    eval_var :: (Binding b, Pretty (Core b Name χ), Forallχ Monoid χ, MonadError (Doc ann) m, Environment Name e) =>
                  Name -> (Maybe (Core b Name χ), (Core b Name χ)) -> e (Sem e b χ) -> m (Sem e b χ)
    eval_var n (Nothing, ty) env = mkvar n ty env
    eval_var _ (Just val, _) env = eval val env
    
    mkvar :: (Binding b, Pretty (Core b Name χ), Forallχ Monoid χ, MonadError (Doc ann) m, Environment Name e) =>
                  Name -> (Core b Name χ) -> e (Sem e b χ) -> m (Sem e b χ)
    mkvar n ty env = do
      ty' <- eval ty env
      pure $ Neutral ty' (NeuVar mempty n)

-- TODO: fix this function - it is wrong!
uni_level :: (Sem e b χ) -> Int
uni_level sem = case sem of 
  SUni _ n -> n + 1
  SPrd _ _ l r -> max (uni_level l) (uni_level r)
  SAbs _ _ _ -> 0 -- note: predicative vs impredicative!!
  Neutral _ _ -> 0 -- TODO: this is probably wrong!!!


{-------------------------------- MISC INSTANCES -------------------------------}
{-                                                                             -}
{-                                                                             -}
{-                                                                             -}
{-------------------------------------------------------------------------------}


instance Pretty (Core b Name χ) => Pretty (Sem e b χ) where
  pretty sem = case sem of 
    SUni _ n -> "𝒰" <> pretty n
    SPrd _ n a b -> pretty n <> " : " <> pretty a <+> "→" <+> pretty b
    SAbs n body _ -> "λ (" <> pretty n <> ")" <+> pretty body
    Neutral _ n -> pretty n
  
instance Pretty (Core b Name χ) => Pretty (Neutral e b χ) where
  pretty neu = case neu of
    NeuVar _ n -> pretty n
    NeuApp _ l r -> pretty l <+> pretty r

instance Pretty (Core b Name χ) => Pretty (Normal e b χ) where
  pretty (Normal _ val) = pretty val

