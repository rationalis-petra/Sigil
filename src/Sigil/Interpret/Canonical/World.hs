{-# LANGUAGE ScopedTypeVariables #-}
module Sigil.Interpret.Canonical.World
  ( World(..)
  , world_packages
  , canon_get_env
  , canon_get_precs
  , canon_get_resolve
  ) where

import Control.Monad.Except (MonadError(..))
import Control.Lens ((^.),makeLenses)
import Control.Monad (join, forM)

import Data.Text (Text, pack)
import qualified Data.Map as Map
import Data.Map (Map)
import qualified Data.Set as Set
import Data.List.NonEmpty (NonEmpty(..))
import Data.Foldable (fold)

import Prettyprinter

import Sigil.Abstract.Syntax
import Sigil.Abstract.Names  
import Sigil.Abstract.Environment  

import Sigil.Parse.Mixfix
import Sigil.Concrete.Internal (InternalPackage)
import Sigil.Interpret.Interpreter (InterpreterErr(..))
import Sigil.Interpret.Canonical.Values  
import Sigil.Interpret.Canonical.Environment  

-- Requires
-- Provides
-- Modules

data World m = World
  { _world_packages :: Map Text (SemPackage m, InternalPackage)
  }
$(makeLenses ''World)

canon_get_env :: (MonadError err m, MonadGen m) => (InterpreterErr -> err) -> World m -> Env (CanonEnv m) m
canon_get_env lift_err world = Env
  { i_lookup = canon_lookup (lift_err . InternalErr)
  , i_insert = canon_insert (lift_err . InternalErr)
  , i_impl = CanonEnv (world^.world_packages) Map.empty
  }
  
get_world_path :: [Package a] -> Package a -> NonEmpty Text -> (Either Text (Maybe (a, [Text])))
get_world_path world package path =
  -- Step 1: check for collisions
  let merged_world = MTree $ fold $ fmap untree exported_modules
      exported_modules = (package^.package_modules) : (fmap get_exports world)
      get_exports package = MTree $ Map.filterWithKey (\k _ -> elem k (package^.package_header.provides)) $ untree $ package^.package_modules

  in if sum (fmap (Map.size . untree) exported_modules) == Map.size (untree merged_world)
  then Right $ get_modulo_path path merged_world
  else Left $ pack $ show $ fmap fst $ Map.toList $ untree merged_world

  
default_precs :: Precedences
default_precs = Precedences
  (Map.fromList
   [ ("sum", PrecedenceNode Set.empty (Set.fromList ["prod"]))
   , ("prod", PrecedenceNode Set.empty (Set.fromList ["ppd"]))
   , ("ppd", PrecedenceNode Set.empty (Set.fromList ["tight"]))
   , ("ctrl", PrecedenceNode Set.empty (Set.fromList ["tight"]))
   , ("tight", PrecedenceNode Set.empty (Set.fromList ["tight"]))
   , ("tight", PrecedenceNode Set.empty (Set.fromList ["close"]))
   , ("close", PrecedenceNode Set.empty Set.empty)
   ])
  "sum" "ppd" "ppd" "close"

canon_get_precs :: (MonadError err m) => (InterpreterErr -> err) -> World m -> Text -> [ImportDef] -> m Precedences
canon_get_precs lift_err world package_name imports = do
  -- For the time being, we don't care about precedence group
  -- We also treat all paths as absolute (not relative to current module).
  -- Therefore, the path of the current module is irrelevant
  package <- case Map.lookup package_name (world^.world_packages) of 
    Just (_, val) -> pure $ val
    Nothing -> throwError $ lift_err $ InternalErr ("Couldn't find package:" <+> pretty package_name)

  -- Get all required packages
  req_packages <- forM (package^.package_header^.requires) $ \name -> do
    case Map.lookup name (world^.world_packages) of 
      Just (_, val) -> pure $ val
      Nothing -> throwError $ lift_err $ InternalErr ("Couldn't find package:" <+> pretty name)
  
  -- Imported Names
  imported_names <- forM imports $ \(Im (path, m)) -> do
    (mdle,p) <- case get_world_path req_packages package path of 
      Right (Just (v,p)) -> pure (v,p)
      Right Nothing -> throwError $ lift_err $ InternalErr ("Can't find import path:" <+> pretty path)
      Left name -> throwError$ lift_err $ InternalErr ("Name clash with package:" <+> pretty name)
    if not (null p) then (throwError $ lift_err $ InternalErr "There was a modulo path; can't deal rn") else pure ()
    case m of
      ImWildcard ->
        pure $ join $ map
          (\case
              Singleχ _ (AnnBind (n, _)) _ -> [name_text n])
          (mdle^.module_entries)
      ImGroup set ->
        pure $ filter (flip Set.member set) $ join $ map
          (\case
              Singleχ _ (AnnBind (n, _)) _ -> [name_text n])
          (mdle^.module_entries)
      _ -> throwError $ lift_err $ InternalErr "Only deal in wildcard + group modifiers!"

  pure $ update_precs (join imported_names) default_precs

canon_get_resolve :: forall m err. MonadError err m => (InterpreterErr -> err) -> World m -> Text -> [ImportDef] -> m (Map Text Path)
canon_get_resolve lift_err world package_name imports = do
  -- Get all required packages
  package <- case Map.lookup package_name (world^.world_packages) of 
    Just (_, val) -> pure val
    Nothing -> throwError $ lift_err $ InternalErr ("Couldn't find package:" <+> pretty package_name)
  req_packages <- forM (package^.package_header^.requires) $ \name -> do
    case Map.lookup name (world^.world_packages) of 
      Just (_, val) -> pure $ val
      Nothing -> throwError $ lift_err $ InternalErr ("Couldn't find package:" <+> pretty name)

  let get_imports :: Map Text Path -> [ImportDef] -> m (Map Text Path)
      get_imports gmap [] = pure gmap
      get_imports gmap (Im (path,im) : imports) = do
        (mdle,p) <- case get_world_path req_packages package path of
          Right (Just (v,p)) -> pure (v,p)
          Right Nothing -> throwError $ lift_err $ InternalErr ("Can't find import path:" <+> pretty path)
          Left name -> throwError$ lift_err $ InternalErr ("Name clash with package:" <+> pretty name)
        if not (null p) then (throwError $ lift_err $ InternalErr "There was a modulo path; can't deal rn") else pure ()
        case im of
          ImWildcard ->
            foldl
              (\mnd entry ->
                 case entry of
                   Singleχ _ (AnnBind (n, _)) _ ->
                     Map.insert (name_text n)
                                (path_snoc (Path (package_name, path)) (name_text n)) <$> mnd)
              (get_imports gmap imports)
              (mdle^.module_entries)
          ImGroup set ->
            foldl
              (\mnd entry ->
                 case entry of
                   Singleχ _ (AnnBind (n, _)) _
                     | Set.member (name_text n) set -> Map.insert (name_text n)
                       (path_snoc (Path (package_name, path)) (name_text n)) <$> mnd
                     | otherwise -> mnd)
              (get_imports gmap imports)
              (mdle^.module_entries)
          _ -> throwError $ lift_err $ InternalErr "only deal in wildcard modifiers!"
  get_imports Map.empty imports
