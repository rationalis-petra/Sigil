module Glyph.Term (
  Term,
  normalize,
  equiv)
  where

import Prelude hiding (head)
import Control.Monad.Except (MonadError, throwError)

import Prettyprinter

import Glyph.Name
import Glyph.Core
  
{------------------------------- THE TERM CLASS --------------------------------}
{- The Term class supports only two methods:                                   -}
{- • normalize: convert to canonical (Β-normal, η-long) form                   -}
{- • equiv: αβη equivalence                                                    -}
{-                                                                             -}
{- Both accept an environment. Currently, this is a local environment, but     -}
{- evantually the environment will also enclude a 'gloval' (i.e. surrounding   -}
{- module) component as well, to look up qualified names (QName)               -}


type Env a = [a]

class Term a where
  normalize :: MonadError (Doc ann) m => Env a -> a -> a -> m a
  equiv :: MonadError (Doc ann) m => Env a -> a -> a -> a -> m Bool


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
  
  
data Sem χ
  = SUni Int
  | SPrd (Sem χ) (Sem χ)
  | SAbs (Core Name χ) (Env (Sem χ))
  | Neutral (Sem χ) (Neutral χ)

data Neutral χ    
  = NeuVar Name
  | NeuApp (Neutral χ) (Normal χ)

data Normal χ = Normal (Sem χ) (Sem χ)


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


instance Eq (Coreχ χ) => Term (Core Name χ) where
  normalize env ty term =
    read_nf (env_size env) =<< (Normal <$> ty' <*> (eval term =<< env_eval env))
    where
      ty' = eval ty =<< env_eval env

      env_size :: Env χ -> Int
      env_size = Prelude.length

  equiv env ty x y = (==) <$> normalize env ty x <*> normalize env ty y


read_nf :: MonadError (Doc ann) m => Int -> Normal χ -> m (Core Name χ)
read_nf n (Normal ty val) = case (ty, val) of 
  (SPrd a b, f) -> do
    let neua = Neutral a $ NeuVar $ DeBruijn n "s"
    f' <- read_nf (n + 1) =<< (Normal <$> (b `app` neua) <*> (f `app` neua))
    pure $ Abs void "s" f'
  (SUni _, SUni i) -> pure $ Uni void i
  (SUni k, SPrd a b) -> do
    a' <- (read_nf n $ Normal (SUni k) a)
    b' <- (read_nf n $ Normal (SPrd a (SUni k)) b)
    pure $ Prd void "s" a' b'
        
  (_, Neutral _ e) -> read_ne n e 
  (_, _) -> throwError "bad read_nf"

read_ne :: MonadError (Doc ann) m => Int -> Neutral χ -> m (Core Name χ)
read_ne n neu = case neu of 
  NeuVar name -> case name of 
    DeBruijn i sym -> pure $ Var void $ DeBruijn (n - (i + 1)) sym 
    _ -> pure $ Var void $ name
  NeuApp l r -> App void <$> (read_ne n l) <*> (read_nf n r) 

eval :: MonadError (Doc ann) m => Core Name χ -> Env (Sem χ) -> m (Sem χ)
eval term env = case term of
  Coreχ _ -> error "cannot eval Coreχ terms" 
  Uni _ n -> pure $ SUni n
  Prd _ _ a b -> SPrd <$> eval a env <*> eval b env
  Var _ name -> env_lookup name env
  Abs _ _ body -> pure $ SAbs body env
  App _ l r -> do
    l' <- (eval l env)
    r' <- (eval r env)
    app l' r'

app :: MonadError (Doc ann) m => Sem χ -> Sem χ -> m (Sem χ)
app (SAbs body env) val = eval body (env_insert val env)
app (Neutral (SPrd a b) neu) v =
  Neutral <$> (b `app` v) <*> pure (NeuApp neu (Normal a v))
app _ _ = throwError "bad args to app"

env_eval :: MonadError (Doc ann) m => Env (Core Name χ) -> m (Env (Sem χ))
env_eval [] = pure []
env_eval (v:vs) = do
  env' <- env_eval vs
  v' <- eval v env'
  pure $ v' : env'

env_insert :: a -> Env a -> Env a
env_insert = (:)

env_lookup :: MonadError (Doc ann) m => Name -> (Env a) -> m a
env_lookup (DeBruijn n _) lst = case drop n lst of 
  [] -> throwError "variable not in scope"
  (x:_) -> pure x
env_lookup (QName _) _ = throwError "can't lookup gloval var!"

void :: a
void = error "bottom value" 
