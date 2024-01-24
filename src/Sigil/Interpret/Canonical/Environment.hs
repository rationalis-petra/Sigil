{-# LANGUAGE ImplicitParams #-}
module Sigil.Interpret.Canonical.Environment
  ( CanonEnv(..)
  , canon_lookup
  , canon_insert
  , canon_insert_path
  , to_semenv ) where

import Control.Monad.Except (MonadError(..))
import Control.Lens((^.))

import qualified Data.Map as Map
import Data.Map (Map)
import Data.Text (Text)
import Data.List (find)

import Prettyprinter
import Prettyprinter.Render.Sigil

import Sigil.Abstract.Names
import Sigil.Abstract.Syntax
import Sigil.Abstract.Environment
import Sigil.Concrete.Internal 
import Sigil.Interpret.Canonical.Values 
import Sigil.Interpret.Canonical.Term 

data CanonEnv m = CanonEnv
  { global_env :: Map Text (SemPackage m, InternalPackage)
  , local_env :: Map UniqueName (Sem m, InternalCore, InternalCore)
  , local_overrides :: Map Path (Sem m, InternalCore, InternalCore)
  }

canon_lookup :: MonadError err m => (SigilDoc -> err) -> Name -> CanonEnv m -> m (Maybe InternalCore)
canon_lookup lift_err (Name name) canon = case name of
  Left (Path (package_name, mpath)) -> case Map.lookup (Path (package_name, mpath)) (local_overrides canon) of 
    Just (_, _, ty) -> pure (Just ty)
    Nothing -> case Map.lookup package_name (global_env canon) of 
      Just (_, package) -> case get_modulo_path mpath (package^.package_modules) of 
        Just (_, []) -> throwError $ lift_err $ "Can't reify a package into a value yet..."
        Just (imodule, [v]) ->
          let
            has_name :: Text -> InternalEntry -> Bool
            has_name name (Singleχ _ (AnnBind (name',_)) _)  | name == name_text name' = True
                                                            | otherwise = False
          in case find (has_name v) (imodule^.module_entries) of
            Just (Singleχ _ (AnnBind (_, ty)) _) -> pure (Just ty)
            Nothing -> pure Nothing
        Just (_, _) -> throwError $ lift_err $ "Can't reify a first-class module lookup"
        Nothing -> pure Nothing
      Nothing -> throwError $ lift_err $ "Unable to locate package:" <+> pretty package_name
  Right unique -> case Map.lookup unique (local_env canon) of
    Just (_, _, ty) -> pure (Just ty)
    Nothing -> pure Nothing

canon_insert :: (MonadError err m, MonadGen m) => (SigilDoc -> err) -> Name -> (Maybe InternalCore, InternalCore) -> CanonEnv m -> m (CanonEnv m)
canon_insert lift_err (Name name) (mval, ty) canon = case name of 
  Left l -> throwError $ lift_err $ "Can't insert variable" <+> pretty l <+> "at path, only as local name"
  Right unique -> do
    let sem_env = (fmap (\(x,_,_) -> x) (local_env canon), fmap (\(x,_,_) -> x) (local_overrides canon), fmap (\(x,_) -> x) (global_env canon))
    (val', sem) <- case mval of
      Just v -> (v, ) <$> let ?lift_err = lift_err in eval v sem_env
      Nothing -> (Var (Name name), ) . flip Neutral (NeuVar (Name name)) <$> let ?lift_err = lift_err in eval ty sem_env
    
    pure $ CanonEnv (global_env canon) (Map.insert unique (sem, val', ty) (local_env canon)) (local_overrides canon)

canon_insert_path :: (MonadError err m, MonadGen m) => (SigilDoc -> err) -> Path -> (InternalCore, InternalCore) -> CanonEnv m -> m (CanonEnv m)
canon_insert_path lift_err unique (val, ty) canon = do
  let sem_env = (fmap (\(x,_,_) -> x) (local_env canon), fmap (\(x,_,_) -> x) (local_overrides canon), fmap (\(x,_) -> x) (global_env canon))
      
  sem <- let ?lift_err = lift_err in eval val sem_env
  pure $ CanonEnv (global_env canon) (local_env canon) (Map.insert unique (sem, val, ty) (local_overrides canon))

to_semenv :: CanonEnv m -> SemEnv m
to_semenv canon = (fmap (\(x,_,_) -> x) (local_env canon), fmap (\(x,_,_) -> x) (local_overrides canon), fmap fst (global_env canon))
