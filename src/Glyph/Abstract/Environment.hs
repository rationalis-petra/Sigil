module Glyph.Abstract.Environment (
  -- Name Types
  OptBind(..),
  AnnBind(..),
  UniqueName,
  QualName,
  Name(..),

  -- Environment
  Environment(..),
  (↦),

  -- Fresh Variable Generation
  MonadGen(..),
  fresh_var,
  freshen,
  Gen,
  run_gen) where


{--------------------------------- ENVIRONMENT ---------------------------------}
{- This file contains abstractions relating to environments and names.         -}
{-                                                                             -}
{-                                                                             -}
{-------------------------------------------------------------------------------}


import Prelude hiding (head, lookup)
import Control.Monad.Except (MonadError, throwError)
import Control.Monad.State (State, runState, get, modify)
  
import Data.Text (Text)
import qualified Data.Map as Map
import Data.Map (Map)

import Prettyprinter  
  

{------------------------------------ NAMES ------------------------------------}
{-                                                                             -}
{-                                                                             -}
{-------------------------------------------------------------------------------}

-- A name with a unique identifier 
type UniqueName = (Integer, Text)

-- A qualified name is one which depends on the value of a toplevel definition
type QualName = [Text]

-- data DBName = QDBName QualName | DeBruijn Int (Maybe Text)
newtype Name = Name (Either QualName UniqueName)
  deriving Eq

-- Bindings: 
-- An optionally annotated binding
newtype OptBind n ty = OptBind (Either n (n, ty))
  deriving Eq

-- An annotated binding
newtype AnnBind n ty = AnnBind (n, ty)   
  deriving Eq


{--------------------------------- GENERATION ----------------------------------}
{-                                                                             -}
{-------------------------------------------------------------------------------}

  
class Monad m => MonadGen m where 
  fresh_id :: m Integer

newtype Gen a = Gen { ungen :: State Integer a }
  deriving (Functor, Applicative, Monad)

instance MonadGen Gen where 
  fresh_id = do
    id <- Gen get
    Gen (modify (+ 1))
    pure id

run_gen :: Gen a -> a
run_gen = fst . flip runState 0 . ungen 

fresh_var :: MonadGen m => Text -> m Name
fresh_var s = fresh_id >>= pure . Name . Right . flip (,) s

freshen :: MonadGen m => Name -> m Name
freshen (Name (Right (_, s))) = fresh_var s
freshen q = pure q


{--------------------------------- ENVIRONMENT ---------------------------------}
{-                                                                             -}
{-                                                                             -}
{-------------------------------------------------------------------------------}


class (Functor e, Foldable e) => Environment n e | e -> n where
  lookup_err :: MonadError (Doc ann) m => n -> e a -> m a 
  lookup :: n -> e a -> Maybe a 
  insert :: n -> a -> e a -> e a
  env_empty :: e a
  eval_helper :: Monad m => (a -> e b -> m b) -> e a -> m (e b)
  

instance Environment Name (Map Integer) where
  lookup_err (Name (Right (n, _))) env = case Map.lookup n env of 
    Nothing -> throwError "variable not in scope"
    Just x -> pure x
  lookup_err (Name (Left _)) _ = throwError "cannot lookup global var!"

  lookup (Name (Right (n, _))) lst = case Map.lookup n lst of 
    Nothing -> Nothing
    Just x -> pure x
  lookup (Name (Left _)) _ = Nothing

  insert (Name (Right (n, _))) v env = Map.insert n v env
  insert _ _ _ = error "cannot insert qualified var"

  env_empty = Map.empty

  eval_helper eval =
    Map.foldlWithKey (\m id val -> m >>= \env' -> do
                         val' <- eval val env'
                         pure $ Map.insert id val' env')
    (pure env_empty)

  
(↦) :: Environment n e => n -> a -> e a
n ↦ v = insert n v env_empty


{---------------------------------- INSTANCES ----------------------------------}
{-                                                                             -}
{-------------------------------------------------------------------------------}

instance (Pretty n, Pretty ty) => Pretty (OptBind n ty) where
  pretty bind = case bind of  
    OptBind (Left n) -> pretty n
    OptBind (Right (n, ty)) -> pretty n <> ":" <> pretty ty

instance (Pretty n, Pretty ty) => Pretty (AnnBind n ty) where
  pretty bind = case bind of
    AnnBind (n, ty) -> pretty n <> ":" <> pretty ty

instance Pretty Name where 
  pretty (Name name) = case name of
    Left qname -> pretty qname -- TODO prettify
    Right (_, var) -> pretty var
