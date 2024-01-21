module Sigil.Abstract.Environment
  -- World 
  ( get_modulo_path
  , insert_at_path
  , get_paths

  -- Environment
  , Env(..)
  , insert
  , lookup
  ) where


{--------------------------------- ENVIRONMENT ---------------------------------}
{-                                                                             -}
{-                                                                             -}
{-------------------------------------------------------------------------------}

import Prelude hiding (head, lookup)
  
import qualified Data.List.NonEmpty as NonEmpty
import Data.List.NonEmpty (NonEmpty(..))
import Data.Text (Text)
import qualified Data.Map as Map

import Sigil.Abstract.Names
import Sigil.Abstract.Syntax 
import Sigil.Concrete.Internal 
  

{---------------------------------- PACKAGES -----------------------------------}
{- MTree manipulation for packages                                             -}
{-                                                                             -}
{-------------------------------------------------------------------------------}

insert_at_path :: NonEmpty Text -> a -> MTree a -> MTree a
insert_at_path path a (MTree subtree) =
  case path of 
    (p :| []) -> case Map.lookup p subtree of 
      Just (_, v) -> MTree $ Map.insert p (Just a, v) subtree
      Nothing -> MTree $ Map.insert p (Just a, Nothing) subtree

    (p :| (t:ts)) -> case Map.lookup p subtree of 
      Just (v, Just subworld) -> MTree $ Map.insert p (v, Just subworld') subtree
        where
          subworld' = insert_at_path (t :| ts) a subworld
      Just (v, Nothing) -> MTree $ Map.insert p (v, Just subworld) subtree
        where 
          subworld = insert_at_path (t :| ts) a (MTree Map.empty)
      Nothing -> MTree $ Map.insert p (Nothing, Just subworld) subtree
        where 
          subworld = insert_at_path (t :| ts) a (MTree Map.empty)

get_modulo_path :: NonEmpty Text -> MTree a -> (Maybe (a, [Text]))
get_modulo_path path (MTree subtree) =
  case path of 
    (p :| []) -> case Map.lookup p subtree of 
      Just ((Just v), _) -> Just (v, [])
      _ -> Nothing
    (p :| (t:ts)) -> case Map.lookup p subtree of 
      Just (_, (Just w)) -> get_modulo_path (t :| ts) w
      Just (Just v, _) -> Just (v, (t : ts))
      _ -> Nothing

get_paths :: MTree a -> [NonEmpty Text]
get_paths (MTree subtree) = Map.foldrWithKey (go []) [] subtree
  where go psf k (mm, mt) out = 
          let out' = maybe out (const $ (NonEmpty.reverse (k :| psf)) : out) mm
          in case mt of
            Just (MTree subtree) -> Map.foldrWithKey (go (k : psf)) out' subtree
            Nothing -> out'
   

{--------------------------------- ENVIRONMENT ---------------------------------}
{-                                                                             -}
{-                                                                             -}
{-------------------------------------------------------------------------------}

data Env env m = Env
  { i_lookup :: Name -> env -> m (Maybe InternalCore)
  , i_insert :: Name -> (Maybe InternalCore, InternalCore) -> env -> m env 
  , i_impl :: env
  }

lookup :: Name -> Env env m -> m (Maybe InternalCore)
lookup n env = (i_lookup env) n (i_impl env)

insert :: Functor m => Name -> (Maybe InternalCore, InternalCore) -> Env env m -> m (Env env m)
insert n val env = Env (i_lookup env) (i_insert env) <$> (i_insert env) n val (i_impl env)

