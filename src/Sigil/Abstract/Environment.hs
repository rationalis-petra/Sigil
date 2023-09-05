module Sigil.Abstract.Environment
  -- Name Types
  ( UniqueName
  , QualName
  , Name(..)

  -- Paths
  , Path

  -- Binding
  , Binding(..)
  , OptBind(..)
  , AnnBind(..)

  -- Environment
  , Environment(..)
  , Env

  -- Fresh Variable Generation
  , MonadGen(..)
  , fresh_var
  , freshen
  , Gen
  , run_gen ) where


{--------------------------------- ENVIRONMENT ---------------------------------}
{- This file contains abstractions relating to environments and names.         -}
{-                                                                             -}
{-                                                                             -}
{-------------------------------------------------------------------------------}


import Prelude hiding (head, lookup)
import Control.Lens
import Control.Monad.Except (MonadError, ExceptT, throwError, lift)
import Control.Monad.State (State, StateT, runState, get, modify)
import Control.Monad.Reader (ReaderT)
  
import Data.List (sortOn)
import Data.List.NonEmpty (NonEmpty)
import Data.Ord (Down(Down))
import Data.Text (Text)
import qualified Data.Map as Map
import Data.Map (Map)

import Prettyprinter  
  
{------------------------------------ PATHS ------------------------------------}
{-                                                                             -}
{-                                                                             -}
{-------------------------------------------------------------------------------}

type Path = NonEmpty

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
  deriving (Eq, Ord)


{------------------------------ BIND ABSTRACTION -------------------------------}
{- There are 3 variants of binding we can have:                                -}
{- + Name but no type, e.g. λ [x] x                                            -}
{- + Type but no name, e.g. ℤ → ℤ                                              -}
{- + Both Name and type, e.g. λ [x:ℤ] (x + 1) or (A:𝒰) → A → A                 -}
{- Specific binding types may encompass any subset of these three, and the     -}
{- typeclass abstraction should account for any possible subset.               -}
{- Hence, name and type return maybes, and the only way to construct a binding -}
{- requires both a name and a type.                                            -}
{-------------------------------------------------------------------------------}


class Binding b where 
  name :: b n a -> Maybe n
  tipe :: b n a -> Maybe a
  bind :: n -> a -> b n a


{----------------------------- CONCRETE BINDINGS -------------------------------}
-- Bindings: 
-- TODO: add bindings with optionally no name!

-- An annotated binding
newtype AnnBind n ty = AnnBind { unann :: (n, ty) }
  deriving Eq

-- Binding instance for AnnBind
instance Functor (AnnBind n) where
  fmap f (AnnBind (n, ty)) = AnnBind (n, f ty)

instance Foldable (AnnBind n) where
  foldr f z (AnnBind (_, ty)) = f ty z
  foldl f z (AnnBind (_, ty)) = f z ty

instance Traversable (AnnBind n) where
  traverse f (AnnBind (n, ty)) = (\r -> AnnBind (n, r)) <$> f ty

instance Binding AnnBind where
  name (AnnBind (n, _)) = Just n
  tipe (AnnBind (_, ty)) = Just ty
  bind n ty = AnnBind (n, ty)

-- An optionally annotated binding
newtype OptBind n ty = OptBind { unOpt :: (Maybe n, Maybe ty) }
  deriving Eq

instance Functor (OptBind n) where
  fmap f (OptBind (n, ty)) = OptBind (n, fmap f ty)

instance Binding OptBind where   
  name (OptBind (n, _)) = n
  tipe (OptBind (_, ty)) = ty
  bind n ty = OptBind (Just n, Just ty)


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

instance MonadGen m => MonadGen (ExceptT e m) where
  fresh_id = lift fresh_id

instance MonadGen m => MonadGen (StateT e m) where
  fresh_id = lift fresh_id

instance MonadGen m => MonadGen (ReaderT e m) where
  fresh_id = lift fresh_id

run_gen :: Gen a -> a
run_gen = fst . flip runState 0 . ungen

fresh_var :: MonadGen m => Text -> m Name
fresh_var s = fresh_id >>= pure . Name . Right . (, s)

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
  union :: e a -> e a -> e a
  -- Traverse + Fold ???
  eval_helper :: Monad m => (n -> a -> e b -> m b) -> e a -> m (e b)
  

data Env a = Env
  { _env_binds :: Map Name (a, Int)
  , _lvl :: Int
  }

$(makeLenses ''Env)

instance Functor Env where   
  fmap f (Env b l) = Env (fmap (_1 %~ f) b) l

instance Foldable Env where
  foldl f z e = foldl f z env'
    where
      env' =
        fmap (fst . snd) $
        sortOn (snd . snd) $
        Map.toList (e^.env_binds)

  -- TODO: mgiht be dodge! (notably: make sure environment level is correct!!)
  foldr f z e = foldr f z env'
    where
      env' =
        fmap (fst . snd) $
        sortOn (Down . snd . snd) $
        Map.toList (e^.env_binds)

-- instance Traversable Env where
--   traverse f env = foldl (\a (id, (val, lvl)) ->
--                             f val <*> a)

--       env' 
  -- eval_helper eval env = foldl (\m (id, (val, lvl)) -> m >>= \env' -> do
  --                                  val' <- eval val env'
  --                                  pure $ re_add id (val', lvl) env') (pure env_empty) env'
    -- where

instance Environment Name Env where
  lookup_err n@(Name (Right _)) env = case Map.lookup n (env^.env_binds) of 
    Nothing -> throwError ("variable not in scope: " <> pretty n)
    Just (x, _) -> pure x
  lookup_err (Name (Left v)) _ = throwError ("cannot lookup global var!" <+> pretty v)

  lookup n@(Name (Right _)) env = case Map.lookup n (env^.env_binds) of 
    Nothing -> Nothing
    Just (x,_) -> pure x
  lookup (Name (Left _)) _ = Nothing

  insert n@(Name (Right _)) v env =
    let lvl' = env^.lvl + 1
        env_binds' = Map.insert n (v, env^.lvl) (env^.env_binds)
    in Env env_binds' lvl'
  insert _ _ _ = error "cannot insert qualified var"

  union (Env binds lvl) (Env binds' lvl') = 
    Env (Map.union binds (fmap (_2 %~ (+) lvl) binds')) (lvl + lvl')

  env_empty = Env Map.empty 0

  -- eval_helper: this must evaluate bindings from /outermost/ to /innermost/,
  -- hence we first convert to a List, sort on lvl and then fold!
  eval_helper eval env =
    foldl (\m (name, (val, lvl)) -> m >>= \env' -> do
              val' <- eval name val env'
              pure $ re_add name (val', lvl) env')
      (pure env_empty) env'
    where
      env' =
        sortOn (snd . snd) $
        Map.toList (env^.env_binds)
      
      re_add name (val, lvl) (Env b _) = Env (Map.insert name (val, lvl) b) lvl

  
{---------------------------------- INSTANCES ----------------------------------}
{-                                                                             -}
{-------------------------------------------------------------------------------}

instance (Pretty n, Pretty ty) => Pretty (OptBind n ty) where
  pretty bind = case bind of  
    OptBind (Just n, Nothing) -> pretty n
    OptBind (Just n, Just ty) -> pretty n <> ":" <> pretty ty
    OptBind (Nothing, Nothing) -> "_"
    OptBind (Nothing, Just ty) -> "_:" <> pretty ty

instance (Pretty n, Pretty ty) => Pretty (AnnBind n ty) where
  pretty bind = case bind of
    AnnBind (n, ty) -> pretty n <> ":" <> pretty ty

instance Pretty Name where 
  pretty (Name name) = case name of
    Left qname -> pretty qname -- TODO prettify
    Right (_, var) -> pretty var
