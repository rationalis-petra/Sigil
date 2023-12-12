{-# OPTIONS_GHC -Wno-unrecognised-pragmas #-}
{-# OPTIONS_GHC -Wno-orphans #-}
module Sigil.Interpret.Canonical
  ( Context(..)
  , CanonM
  , canonical_interpreter
  ) where


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

import Control.Lens (makeLenses, (^.), (.=), (%~), use, at)
import Prettyprinter
--import Topograph : todo: use for dependency analysis in evaluation

import Sigil.Abstract.Names
import Sigil.Abstract.Syntax
import Sigil.Abstract.Environment
import Sigil.Parse.Mixfix
import Sigil.Concrete.Internal
import Sigil.Interpret.Interpreter
import Sigil.Interpret.Unify
import Sigil.Interpret.Term

instance Show InternalCore where    
  show = show . pretty

newtype Context = Context { _world :: Map Text (Package InternalModule) } -- threads :: ??

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

  -- eval :: (err -> err) -> env -> t -> t -> m t
  , eval = \f env ty term ->
      normalize (f . liftErr . EvalErr) env ty term

  -- norm_eq :: (err -> err) -> env -> t -> t -> t -> m Bool
  , norm_eq = \f env ty a b ->
      equiv (f . liftErr . EvalErr) env ty a b

  -- TODO: add environment to unification!!
  -- solve_formula :: (err -> err) -> env -> Formula t -> m (Substitution t)
  , solve_formula = \f _ formula ->
      solve (f . liftErr . EvalErr) formula

  , intern_package = \package_name package -> do
      (world.at package_name) .= Just package 

  , intern_module = \package_name path modul -> do
      packages <- use world
      pkg' <- case Map.lookup package_name packages of 
        Just package -> pure $ (package_modules %~ (insert_at_path path modul)) package
        Nothing -> throwError $ liftErr $ InternalErr ("couldn't find package:" <+> pretty package_name)
      (world.at package_name) .= Just pkg'

  , get_env = \package_name imports -> do
      packages <- use world
      modules <- case Map.lookup package_name packages of
        Just val -> pure $ val^.package_modules
        Nothing -> throwError $ liftErr $ InternalErr ("couldn't find package:" <+> pretty package_name)
      pure $ Env Map.empty 0 (to_globmap modules) imports (to_eworld modules)

  , get_precs = \package_name imports -> do
      -- For the time being, we don't care about precedence group
      -- We also treat all paths as absolute (not relative to current module).
      -- Therefore, the path of the current module is irrelevant
      packages <- use world
      package <- case Map.lookup package_name packages of 
        Just val -> pure $ val^.package_modules
        Nothing -> throwError $ liftErr $ InternalErr ("couldn't find package:" <+> pretty package_name)

      imported_names <- forM imports $ \(Im (path, m)) -> do
        (mdle,p) <- case get_modulo_path path package of 
          Nothing -> throwError $ liftErr $ InternalErr ("can't find import path:" <+> pretty (show path))
          Just (v,p) -> pure (v,p)
        if not (null p) then (throwError $ liftErr $ InternalErr "there was a modulo path; can't deal rn") else pure ()
        case m of
          ImWildcard -> 
            pure $ join $ map
              (\case
                  Singleχ _ (AnnBind (n, _)) _ -> [name_text n])
              (mdle^.module_entries)
          _ -> throwError $ liftErr $ InternalErr "only deal in wildcard modifiers!"

      pure $ update_precs (join imported_names) default_precs

  , get_resolve = \package_name imports -> do
      packages <- use world
      modules <- case Map.lookup package_name packages of 
        Just val -> pure (val^.package_modules)
        Nothing -> throwError $ liftErr $ InternalErr ("couldn't find package:" <+> pretty package_name)
      let get_imports :: Map Text QualName -> [ImportDef] -> CanonM err (Map Text QualName)
          get_imports gmap [] = pure gmap
          get_imports gmap (Im (path,im) : imports) = do
            (mdle,p) <- case get_modulo_path path modules of
              Nothing -> throwError $ liftErr $ InternalErr ("can't find import path: " <> pretty (show path))
              Just (v,p) -> pure (v,p)
            if not (null p) then (throwError $ liftErr $ InternalErr "there was a modulo path; can't deal rn") else pure ()
            case im of
              ImWildcard ->
                foldl
                  (\mnd entry ->
                     case entry of
                       Singleχ _ (AnnBind (n, _)) _ ->
                         Map.insert (name_text n)
                                    (NonEmpty.append (unPath path) (name_text n :| [])) <$> mnd)
                  (get_imports gmap imports)
                  (mdle^.module_entries)
              _ -> throwError $ liftErr $ InternalErr "only deal in wildcard modifiers!"
      get_imports Map.empty imports

  , get_module_env = \package_name module_path -> do
      packages <- use world
      modules <- case Map.lookup package_name packages of 
        Just val -> pure (val^.package_modules)
        Nothing -> throwError $ liftErr $ InternalErr ("couldn't find package:" <+> pretty package_name)
      imodule <- case get_modulo_path module_path modules of 
          Nothing -> throwError $ liftErr $ InternalErr ("can't find import path:" <+> pretty (show module_path))
          Just (v,p) -> if null p then pure v else throwError $ liftErr $ InternalErr ("module path finding:" <+> pretty (show module_path))
      
      let insert_entry entry env = case entry of  
            Singleχ _ (AnnBind (n,ty)) val -> insert n (Just ty, val) env 
          pre_env = Env Map.empty 0 (to_globmap modules) (imodule^.module_imports) (to_eworld modules)
      pure $ foldr insert_entry pre_env (imodule^.module_entries)

  , get_module_precs = \package_name module_path -> do
      -- For the time being, we don't care about precedence group
      -- We also treat all paths as absolute (not relative to current module).
      -- Therefore, the path of the current module is irrelevant
      packages <- use world
      modules <- case Map.lookup package_name packages of 
        Just val -> pure (val^.package_modules)
        Nothing -> throwError $ liftErr $ InternalErr ("couldn't find package:" <+> pretty package_name)
      imodule <- case get_modulo_path module_path modules of 
          Nothing -> throwError $ liftErr $ InternalErr ("can't find import path:" <+> pretty (show module_path))
          Just (v,p) -> if null p then pure v else throwError $ liftErr $ InternalErr ("can't find import path: " <> pretty (show module_path))
  
      imported_names <- forM (imodule^.module_imports) $ \(Im (path, m)) -> do
        (mdle,p) <- case get_modulo_path path modules of 
          Nothing -> throwError $ liftErr $ InternalErr ("can't find import path: " <> pretty (show path))
          Just (v,p) -> pure (v,p)
        if null p then pure () else (throwError $ liftErr $ InternalErr "there was a modulo path; can't deal rn")
        case m of
          ImWildcard -> 
            pure $ join $ map
              (\case
                  Singleχ _ (AnnBind (n, _)) _ -> [name_text n])
              (mdle^.module_entries)
          _ -> throwError $ liftErr $ InternalErr "only deal in wildcard modifiers!"

      pure $ update_precs (join imported_names) default_precs

  , get_module_resolve = \package_name module_path -> do
      packages <- use world
      modules <- case Map.lookup package_name packages of 
        Just val -> pure (val^.package_modules)
        Nothing -> throwError $ liftErr $ InternalErr ("couldn't find package:" <+> pretty package_name)
      imodule <- case get_modulo_path module_path modules of 
          Nothing -> throwError $ liftErr $ InternalErr ("can't find import path:" <+> pretty (show module_path))
          Just (v,p) -> if null p then pure v else throwError $ liftErr $ InternalErr ("can't find import path: " <> pretty (show module_path))
      let get_imports :: Map Text QualName -> [ImportDef] -> CanonM err (Map Text QualName)
          get_imports gmap [] = pure gmap
          get_imports gmap (Im (path,im) : imports) = do
            (mdle,p) <- case get_modulo_path path modules of
              Nothing -> throwError $ liftErr $ InternalErr ("can't find import path: " <> pretty (show path))
              Just (v,p) -> pure (v,p)
            if not (null p) then (throwError $ liftErr $ InternalErr "there was a modulo path; can't deal rn") else pure ()
            case im of
              ImWildcard ->
                foldl
                  (\mnd entry ->
                     case entry of
                       Singleχ _ (AnnBind (n, _)) _ ->
                         Map.insert (name_text n)
                                    (NonEmpty.append (unPath path) (name_text n :| [])) <$> mnd)
                  (get_imports gmap imports)
                  (mdle^.module_entries)
              _ -> throwError $ liftErr $ InternalErr "only deal in wildcard modifiers!"
      get_imports Map.empty (imodule^.module_imports)
  
  , get_available_modules = \package_name -> do
      packages <- use world
      case Map.lookup package_name packages of 
        Just package -> pure $ get_paths (package^.package_modules)
        Nothing -> throwError $ liftErr $ InternalErr ("couldn't find package:" <+> pretty package_name)

  , get_available_packages = do
      packages <- use world
      pure $ Map.foldrWithKey (\k _ l -> (k: l)) [] packages

  , run = \s mon -> 
      pure $ case run_gen $ runExceptT $ runStateT mon s of 
        Right (v,s) -> (Right v, s)
        Left err -> (Left err, s)

  , start_state = Context Map.empty
  , stop = pure ()

  , to_image = error "to_image not implemented"
  , from_image = error "to_image not implemented"
  }

to_globmap :: MTree InternalModule -> Map Path (Maybe InternalCore, InternalCore)
to_globmap (MTree root) = Map.foldrWithKey (go []) Map.empty root
  where 
    go :: [Text] -> Text -> (Maybe InternalModule, Maybe (MTree InternalModule))
       -> Map Path (Maybe InternalCore, InternalCore)
       -> Map Path (Maybe InternalCore, InternalCore)
    go psf name (mim, mw) gmap = gmap''
      where 
        gmap' = case mim of 
          Just modul -> foldl (add_entry (name : psf)) gmap (modul^.module_entries)
          Nothing -> gmap
        gmap'' = case mw of 
          Just (MTree child) -> Map.foldrWithKey (go (name : psf)) gmap' child
          Nothing -> gmap'
    
    add_entry :: [Text] -> Map Path (Maybe InternalCore, InternalCore) -> InternalEntry -> Map Path (Maybe InternalCore, InternalCore)
    add_entry psf gmap entry = case entry of
      Singleχ _ (AnnBind (n, ty)) val -> Map.insert (Path $ NonEmpty.reverse (name_text n :| psf)) (Just val, ty) gmap 
    

to_eworld :: MTree InternalModule -> MTree (EModule (Maybe InternalCore, InternalCore))
to_eworld world = flip fmap world $ \mod ->
  EModule (mod^.module_header) (mod^.module_imports) (mod^.module_exports) $ flip fmap (mod^.module_entries) $ \case
   Singleχ _ (AnnBind (n,ty)) val -> (n, (name_text n), (Just val, ty))
