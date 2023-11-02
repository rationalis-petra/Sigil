{-# OPTIONS_GHC -Wno-unrecognised-pragmas #-}
{-# OPTIONS_GHC -Wno-orphans #-}
module Sigil.Interpret.Canonical
  ( Context(..)
  , CanonM
  , canonical_interpreter ) where


{---------------------------- CANONICAL INTERPRETER ----------------------------}
{- This file contains the definition for the 'canonical' interpreter. It is    -}
{- a simple tree-walking interpreter whose behaviour should serve as a         -}
{- reference point to other interpreters. It is also a fall-back interpreter,  -}
{- Guaranteed to run on any platform, and so is useful if, the libraries       -}
{- needed to run the other interpreters (e.g. JVM) aren't available on the     -}
{- current machine.                                                            -}
{-------------------------------------------------------------------------------}

import Control.Monad.State (StateT, runStateT)
import Control.Monad.Except (ExceptT, throwError, runExceptT)
import Control.Monad (join, forM)
import qualified Data.List.NonEmpty as NonEmpty
import Data.List.NonEmpty (NonEmpty(..))
import qualified Data.Map as Map
import Data.Map (Map)
import qualified Data.Set as Set
import Data.Text (Text)

import Control.Lens (makeLenses, (^.), (%=), use)
import Prettyprinter
--import Topograph

import Sigil.Abstract.Names
import Sigil.Abstract.Syntax
import Sigil.Abstract.Environment
import Sigil.Parse.Mixfix
import Sigil.Concrete.Internal
import Sigil.Interpret.Interpreter
import Sigil.Interpret.Term

-- the type of module. Contains both
-- a regular 'internal' module 
-- a 'semantic' module, i.e. a pre-evaluated module

instance Show InternalCore where    
  show = show . pretty


newtype Context = Context { _world :: World InternalModule } -- threads :: ??

$(makeLenses ''Context)

type CanonM err = StateT Context (ExceptT err Gen)

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


canonical_interpreter :: forall err. (InterpreterErr -> err)
  -> Interpreter (CanonM err) err (Env (Maybe InternalCore, InternalCore)) Context InternalCore
canonical_interpreter liftErr = Interpreter
  { reify = pure
  , reflect = pure

  , eval = \f env ty term -> do
      normalize (f . liftErr . EvalErr) env ty term

  , norm_eq = \f env ty a b -> do
      equiv (f . liftErr . EvalErr) env ty a b

  , intern_module = \path modul ->
      world %= insert_at_path path modul

  , get_env = \_ imports -> do
      world <- use world
      let to_globmap :: World InternalModule -> Map (Path Text) (Maybe InternalCore, InternalCore)
          to_globmap (World root) = Map.foldrWithKey (go []) Map.empty root
            where 
              go :: [Text] -> Text -> (Maybe InternalModule, Maybe (World InternalModule))
                 -> Map (Path Text) (Maybe InternalCore, InternalCore)
                 -> Map (Path Text) (Maybe InternalCore, InternalCore)
              go psf name (mim, mw) gmap = gmap''
                where 
                  gmap' = case mim of 
                    Just modul -> foldl (add_entry (name : psf)) gmap (modul^.module_entries)
                    Nothing -> gmap
                  gmap'' = case mw of 
                    Just (World child) -> Map.foldrWithKey (go (name : psf)) gmap' child
                    Nothing -> gmap'
              
              add_entry :: [Text] -> Map (Path Text) (Maybe InternalCore, InternalCore) -> InternalEntry -> Map (Path Text) (Maybe InternalCore, InternalCore)
              add_entry psf gmap entry = case entry of
                Singleχ _ (AnnBind (n, ty)) val -> Map.insert (NonEmpty.reverse (name_text n :| psf)) (Just val, ty) gmap 
                Mutualχ _ _ -> error "add_entry not implemented for mutual!"
              

          to_eworld :: World InternalModule -> World (EModule (Maybe InternalCore, InternalCore))
          to_eworld world = flip fmap world $ \mod ->
            EModule (mod^.module_header) (mod^.module_imports) (mod^.module_exports) $ flip fmap (mod^.module_entries) $ \case
             Singleχ _ (AnnBind (n,ty)) val -> (n, (name_text n), (Just val, ty))
             Mutualχ _ _ -> error "to_globmap not implemented for mutual!"

      pure $ Env Map.empty 0 (to_globmap world) imports (to_eworld world)

  , get_precs = \_ imports -> do
      -- For the time being, we don't care about precedence group
      -- We also treat all paths as absolute (not relative to current module).
      -- Therefore, the path of the current module is irrelevant
      world <- use world
      imported_names <- forM imports $ \(path, m) -> do
        (mdle,p) <- case get_modulo_path path world of 
          Nothing -> throwError $ liftErr $ InternalErr ("can't find import path: " <> pretty (show path))
          Just (v,p) -> pure (v,p)
        if not (null p) then (throwError $ liftErr $ InternalErr "there was a modulo path; can't deal rn") else pure ()
        case m of
          ImWildcard -> 
            pure $ join $ map
              (\case
                  Singleχ _ (AnnBind (n, _)) _ -> [name_text n]
                  Mutualχ _ bs -> map (\(n,_,_) -> name_text n) bs)
              (mdle^.module_entries)
          _ -> throwError $ liftErr $ InternalErr "only deal in wildcard modifiers!"

      pure $ update_precs (join imported_names) default_precs

  , get_resolve = \_ imports -> do
      world <- use world
      let get_imports :: Map Text (Path Text) -> [ImportDef] -> CanonM err (Map Text (Path Text))
          get_imports gmap [] = pure gmap
          get_imports gmap ((path,im) : imports) = do
            (mdle,p) <- case get_modulo_path path world of
              Nothing -> throwError $ liftErr $ InternalErr ("can't find import path: " <> pretty (show path))
              Just (v,p) -> pure (v,p)
            if not (null p) then (throwError $ liftErr $ InternalErr "there was a modulo path; can't deal rn") else pure ()
            case im of
              ImWildcard ->
                foldl
                  (\mnd entry ->
                     case entry of
                       Singleχ _ (AnnBind (n, _)) _ -> Map.insert (name_text n) (NonEmpty.append path (name_text n :| [])) <$> mnd
                       Mutualχ _ _ -> error "mutual in get_resolve/get_imports")
                  (get_imports gmap imports)
                  (mdle^.module_entries)
              _ -> throwError $ liftErr $ InternalErr "only deal in wildcard modifiers!"
      get_imports Map.empty imports 

  , run = \s mon -> 
      pure $ case run_gen $ runExceptT $ runStateT mon s of 
        Right (v,s) -> (Right v, s)
        Left err -> (Left err, s)

  , start_state = Context (World Map.empty)
  , stop = pure ()

  , to_image = error "to_image not implemented"
  , from_image = error "to_image not implemented"
  }

