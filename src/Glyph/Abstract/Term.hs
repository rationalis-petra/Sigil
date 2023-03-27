{-# LANGUAGE ScopedTypeVariables #-}
module Glyph.Abstract.Term
  (Term(..)) where

import Prelude hiding (head, lookup)
import Control.Monad.Except (MonadError, throwError)

import Prettyprinter

import Glyph.Abstract.Syntax
import Glyph.Abstract.Environment
  

{------------------------------- THE TERM CLASS --------------------------------}
{- The Term class supports only two methods:                                   -}
{- • normalize: convert to canonical (Β-normal, η-long) form                   -}
{- • equiv: αβη equivalence                                                    -}
{-                                                                             -}
{- Both accept an environment. Currently, this is a local environment, but     -}
{- eventually the environment will also include a 'global' (i.e. surrounding   -}
{- module) component as well, to look up qualified names (QName)               -}
{-------------------------------------------------------------------------------}


class Term a where
  normalize :: (MonadError (Doc ann) m, Environment Name e) => e a -> a -> a -> m a
  equiv :: (MonadError (Doc ann) m, Environment Name e) => e a -> a -> a -> a -> m Bool


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


data Sem e χ
  = SUni Int
  | SPrd Name (Sem e χ) (Sem e χ)
  | SAbs Name (Core AnnBind Name χ) (e (Sem e χ))
  | Neutral (Sem e χ) (Neutral e χ)

data Neutral e χ
  = NeuVar Name
  | NeuApp (Neutral e χ) (Normal e χ)

data Normal e χ = Normal (Sem e χ) (Sem e χ)


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
{-------------------------------------------------------------------------------}


-- TODO: now we use IDs for names, need to ensure we do capture-avoiding substitution!!
instance Eq (Core AnnBind Name χ) => Term (Core AnnBind Name χ) where
  normalize env ty term =
    read_nf =<< (Normal <$> ty' <*> term')
    where
      ty' = eval ty =<< env_eval env
      term' = (eval term =<< env_eval env)

  equiv env ty x y = (==) <$> normalize env ty x <*> normalize env ty y


read_nf :: forall e χ m ann. (MonadError (Doc ann) m, Environment Name e) => Normal e χ -> m (Core AnnBind Name χ)
read_nf (Normal ty val) = case (ty, val) of 
  (SPrd name a b, f) -> do
    let neua :: Sem e χ 
        neua = Neutral a $ NeuVar name
    
        lvl = uni_level a
    a' <- read_nf $ Normal (SUni lvl) a
    f' <- read_nf =<< (Normal <$> (b `app` neua) <*> (f `app` neua))
    pure $ Abs void (AnnBind (name, a')) f'
  (SUni _, SUni i) -> pure $ Uni void i
  (SUni k, SPrd name a b) -> do
    a' <- (read_nf $ Normal (SUni k) a)
    b' <- (read_nf $ Normal (SPrd name a (SUni k)) b)
    pure $ Prd void (AnnBind (name, a')) b'
        
  (_, Neutral _ e) -> read_ne e 
  (_, _) -> throwError "bad read_nf"

read_ne :: (MonadError (Doc ann) m, Environment Name e) => Neutral e χ -> m (Core AnnBind Name χ)
read_ne neu = case neu of 
  NeuVar name -> pure $ Var void name
  NeuApp l r -> App void <$> (read_ne l) <*> (read_nf r) 

eval :: (MonadError (Doc ann) m, Environment Name e) => Core AnnBind Name χ -> e (Sem e χ) -> m (Sem e χ)
eval term env = case term of
  Coreχ _ -> throwError "cannot eval Coreχ terms" 
  Uni _ n -> pure $ SUni n
  Prd _ (AnnBind (name, a)) b -> SPrd name <$> eval a env <*> eval b env
  Var _ name -> lookup_err name env
  Abs _ (AnnBind (name, _)) body -> pure $ SAbs name body env
  App _ l r -> do
    l' <- (eval l env)
    r' <- (eval r env)
    app l' r'

app :: (MonadError (Doc ann) m, Environment Name e) => Sem e χ -> Sem e χ -> m (Sem e χ)
app (SAbs name body env) val = eval body (insert name val env)
app (Neutral (SPrd _ a b) neu) v =
  Neutral <$> (b `app` v) <*> pure (NeuApp neu (Normal a v))
app _ _ = throwError "bad args to app"

env_eval :: (MonadError (Doc ann) m, Environment Name e) => e (Core AnnBind Name χ) -> m (e (Sem e χ))
env_eval = eval_helper eval

-- TODO: fix this function - it is wrong!
uni_level :: (Sem e χ) -> Int
uni_level sem = case sem of 
  SUni n -> n + 1
  SPrd _ l r -> max (uni_level l) (uni_level r)
  SAbs _ _ _ -> 0 -- note: predicative vs impredicative!!
  Neutral _ _ -> 0 -- TODO: this is probably wrong!!!
  
void :: a
void = error "bottom value" 

