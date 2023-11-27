module Sigil.Abstract.Environment
  -- World 
  ( get_modulo_path
  , insert_at_path
  , get_paths

  -- Environment
  , Environment(..)
  , EModule(..)
  , epath, evals , eimports, eexports
  , Env(..)
  , globals
  , eval_helper
  ) where

{--------------------------------- ENVIRONMENT ---------------------------------}
{-                                                                             -}
{-                                                                             -}
{-------------------------------------------------------------------------------}

import Prelude hiding (head, lookup)
import Control.Lens hiding ((<|))
import Control.Monad.Except (MonadError, throwError)
  
import Data.Foldable (fold, find)
import Data.List (sortOn)
import qualified Data.List.NonEmpty as NonEmpty
import Data.List.NonEmpty (NonEmpty(..), (<|))
import Data.Text (Text)
import qualified Data.Set as Set
import Data.Set (Set)
import qualified Data.Map as Map
import Data.Map (Map)

import Prettyprinter  
import Topograph  

import Sigil.Abstract.Names
import Sigil.Abstract.Syntax 
  

{------------------------------------ WORLD ------------------------------------}
{-                                                                             -}
{-                                                                             -}
{-------------------------------------------------------------------------------}

insert_at_path :: Path -> a -> MTree a -> MTree a
insert_at_path path a (MTree subtree) =
  case path of 
    Path (p :| []) -> case Map.lookup p subtree of 
      Just (_, v) -> MTree $ Map.insert p (Just a, v) subtree
      Nothing -> MTree $ Map.insert p (Just a, Nothing) subtree

    Path (p :| (t:ts)) -> case Map.lookup p subtree of 
      Just (v, Just subworld) -> MTree $ Map.insert p (v, Just subworld') subtree
        where
          subworld' = insert_at_path (Path $ t :| ts) a subworld
      Just (v, Nothing) -> MTree $ Map.insert p (v, Just subworld) subtree
        where 
          subworld = insert_at_path (Path $ t :| ts) a (MTree Map.empty)
      Nothing -> MTree $ Map.insert p (Nothing, Just subworld) subtree
        where 
          subworld = insert_at_path (Path $ t :| ts) a (MTree Map.empty)

get_modulo_path :: Path -> MTree a -> (Maybe (a, [Text]))
get_modulo_path path (MTree subtree) =
  case path of 
    Path (p :| []) -> case Map.lookup p subtree of 
      Just ((Just v), _) -> Just (v, [])
      _ -> Nothing
    Path (p :| (t:ts)) -> case Map.lookup p subtree of 
      Just (_, (Just w)) -> get_modulo_path (Path $ t :| ts) w
      Just (Just v, _) -> Just (v, (t : ts))
      _ -> Nothing

get_paths :: MTree a -> [Path]
get_paths (MTree subtree) = 
  let go :: Text -> (Maybe a, Maybe (MTree a)) -> [Path]
      go name (_, snd) = case snd of
        Just world -> map (Path . (name <|) . unPath) (get_paths world)
        Nothing -> [(Path $ name :| [])]
  in fold (Map.mapWithKey go subtree)

data EModule a = EModule
  { _epath :: Path
  , _eimports :: [ImportDef]
  , _eexports :: [ExportDef]
  , _evals :: [(Name, Text, a)]
  }

data Env a = Env
  { _env_binds :: Map Name (a, Int)
  , _lvl :: Int -- Level is used to sort keys for evaluation when necessary
  , _globals :: Map Path a
  , _env_imports :: [ImportDef]
  , _world :: MTree (EModule a)
  }

$(makeLenses ''Env)
$(makeLenses ''EModule)


{--------------------------------- ENVIRONMENT ---------------------------------}
{-                                                                             -}
{-                                                                             -}
{-------------------------------------------------------------------------------}

class Environment n e | e -> n where
  lookup_err :: MonadError err m => (Doc ann -> err) -> n -> e a -> m a 
  lookup :: n -> e a -> Maybe a 
  insert :: n -> a -> e a -> e a
  env_empty :: e a
  -- TODO: change this method to work with local + global environments!
  -- notably, the NAME is causing issues!

instance (Pretty n, Ord n) => Environment n (Map n) where
  lookup_err lift_err n env = case Map.lookup n env of
    Nothing -> throwError $ lift_err $ ("variable not in scope:" <+> pretty n)
    Just v -> pure v
  lookup = Map.lookup
  insert = Map.insert
  env_empty = Map.empty

instance Environment Name Env where
  lookup_err lift_err n env = case Map.lookup n (env^.env_binds) of 
    Just (x, _) -> pure x
    Nothing -> case n of
      Name (Left p) -> case Map.lookup (Path p) (env^.globals) of
        Nothing -> throwError $ lift_err $ ("global variable not in scope:" <+> pretty n)
        Just v -> pure v
      _ -> throwError $ lift_err $ ("local variable not in scope:" <+> pretty n)

  lookup n env = case Map.lookup n (env^.env_binds) of 
    Just (x,_) -> pure x
    Nothing -> case n of
      Name (Left p) -> Map.lookup (Path p) (env^.globals)
      _ -> Nothing

  insert n v env =
    let lvl' = env^.lvl + 1
        env_binds' = Map.insert n (v, env^.lvl) (env^.env_binds)
    in Env env_binds' lvl' (env^.globals) (env^.env_imports) (env^.world)

  env_empty = Env Map.empty 0 Map.empty [] (MTree Map.empty)

  

eval_helper :: forall err ann m a b. MonadError err m => (Doc ann -> err) -> (Map Name b -> Name -> a -> m b) -> Env a -> m (Map Name b)
eval_helper lift_err eval env = do
  -- Step 1: construct dependency graph
  let construct_graph :: MTree (EModule a) -> Map Path (Set Path)
      construct_graph (MTree trees) = Map.foldrWithKey (go []) Map.empty trees
        where
          go :: [Text] -> Text -> (Maybe (EModule a), Maybe (MTree (EModule a))) -> Map Path (Set Path) -> Map Path (Set Path)
          go psf name (m, t) map = map''
            where
              map' = case m of
                Just modul -> Map.insert
                  (Path $ NonEmpty.reverse (name :| psf))
                  (dependencies modul) map
                Nothing -> map
              map'' = case t of
                Just (MTree subtree) -> Map.foldrWithKey (go (name : psf)) map' subtree
                Nothing -> map'

          dependencies :: EModule a -> Set Path
          dependencies = Set.fromList . map (fst . unImport) . (view eimports)

  -- Step 2: evaluate modules
  let eval_graph :: MTree (EModule a) -> G Path i -> m (MTree (EModule b))
      eval_graph old (G {..}) = go old (MTree $ Map.empty) (map gFromVertex gVertices)

      go :: MTree (EModule a) -> MTree (EModule b) -> [Path] -> m (MTree (EModule b))
      go _ world [] = pure world
      go old_world world (path:paths) = do 
        mod <- case get_modulo_path path old_world of 
          Just (val,[]) -> pure val
          _ -> throwError $ lift_err ("failed to get module:" <+> pretty path)
        mod' <- eval_emodule world mod 
        let world' = insert_at_path path mod' world 
        go old_world world' paths

      eval_emodule :: MTree (EModule b) -> EModule a -> m (EModule b)
      eval_emodule world (EModule path imports exports vals) = do 
        env <- get_globals imports world
        let eval_vals :: Map Name b -> [(Name, Text, a)] -> m [(Name, Text, b)]
            eval_vals _ [] = pure []
            eval_vals env ((name, text, val) : vals) = do
              val' <- eval env name val
              ((name, text, val') :) <$> eval_vals (Map.insert name val' env) vals
        EModule path imports exports <$> eval_vals env vals

  -- Step 3: use imports to get current environment
      get_globals :: [ImportDef] -> MTree (EModule b) -> m (Map Name b)
      get_globals [] _ = pure Map.empty
      get_globals (Im (path, im) : is) world = case im of 
        -- TODO: respect export modifiers of module!
        ImSingleton -> case get_modulo_path path world of 
          Just (modul, [nme]) -> case find (\(_, t, _) -> t == nme) (modul^.evals) of 
            Just (_, t, val) -> Map.insert (Name (Left (NonEmpty.append (unPath path) (t :| [])))) val <$> (get_globals is world)
            _ -> throwError $ lift_err ("singleton import of" <+> pretty path <+> "failed")
          _ -> throwError $ lift_err ("singleton import of" <+> pretty path <+> "failed")
        ImWildcard -> case get_modulo_path path world of 
          Just (modul, []) ->
            foldl (\m (_, t, val) -> Map.insert (Name (Left (NonEmpty.append (unPath path) (t :| [])))) val <$> m)
                  (get_globals is world) (modul^.evals)
          _ -> throwError $ lift_err ("wildcard import of" <+> pretty path <+> "failed")
        _ -> throwError $ lift_err "cannot import non-singleton/wildcard yet!"

  -- Step 4: evaluate the local environment
      add_locals :: Map Name b -> m (Map Name b)
      add_locals new_env = go new_env $ sortOn (snd . snd) $ Map.toList (env^.env_binds)
        where 
          go :: Map Name b -> [(Name, (a, Int))] -> m (Map Name b)
          go env [] = pure env 
          go env ((name, (val, _)) : vals) = do 
            val' <- eval env name val
            go (Map.insert name val' env) vals

  -- Step 5: put it all together!
  let
    res :: Either [Path] (m (Map Name b))
    res = runG (construct_graph (env^.world)) $ \graph -> do
        world' <- eval_graph (env^.world) graph
        env <- get_globals (env^.env_imports) world'
        add_locals  env
  case res of 
    Left path -> throwError $ lift_err ("cycle in dependency graph:" <> pretty path)
    Right m -> m
   

  
