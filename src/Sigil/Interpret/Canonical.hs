{-# OPTIONS_GHC -Wno-unrecognised-pragmas #-}
{-# OPTIONS_GHC -Wno-orphans #-}
{-# LANGUAGE ImplicitParams #-}
module Sigil.Interpret.Canonical
  ( CanonM
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

import Prelude hiding (lookup)
import Control.Monad.State (StateT, MonadState, runStateT, get)
import Control.Monad.Except (ExceptT, MonadError, throwError, runExceptT)
import Control.Applicative (Alternative)
import qualified Data.Map as Map

import Control.Lens ((^.), (.=), (.~), (%~), use, at)
import Prettyprinter

import Sigil.Abstract.Names
import Sigil.Abstract.Syntax
import Sigil.Abstract.Environment hiding (insert)
import Sigil.Concrete.Internal
import Sigil.Interpret.Interpreter
import Sigil.Interpret.Unify

import Sigil.Interpret.Canonical.Values
import Sigil.Interpret.Canonical.Term
import Sigil.Interpret.Canonical.Environment
import Sigil.Interpret.Canonical.World

instance Show InternalCore where    
  show = show . pretty

newtype CanonM err a = CannonM { unCanonM :: StateT (World (CanonM err)) (ExceptT err Gen) a }
  deriving (Functor, Applicative, Alternative, Monad, MonadState (World (CanonM err)), MonadError err, MonadGen)

canonical_interpreter :: forall err. (Monoid err) => (InterpreterErr -> err)
  -> Interpreter (CanonM err) err (CanonEnv (CanonM err)) (World (CanonM err))
canonical_interpreter lift_err = Interpreter
  { -- eval :: (err -> err) -> env -> t -> t -> m t
  eval = \f env ty term ->
      normalize (f . lift_err . EvalErr) (to_semenv env) ty term

  -- norm_eq :: (err -> err) -> env -> t -> t -> t -> m Bool
  , norm_eq = \f env ty a b ->
      equiv (f . lift_err . EvalErr) (to_semenv env) ty a b

  -- TODO: add environment to unification!!
  -- solve_formula :: (err -> err) -> env -> Formula t -> m (Substitution t)
  , solve_formula = \f _ formula ->
      solve (f . lift_err . EvalErr) formula

  , make_package = \package_name -> do
      (world_packages.at package_name) .=
        Just (SemPackage [] [] (MTree (Map.empty)), Package (PackageHeader package_name [] []) (MTree Map.empty))

  , intern_package = \package_name package -> do
      env <- CanonEnv <$> use world_packages <*> pure Map.empty <*> pure Map.empty
      sem_package <- let ?lift_err = lift_err . EvalErr in eval_package (to_semenv env) package
      (world_packages.at package_name) .= Just (sem_package, package)

  , get_package = \package_name -> do
      pkg <- use (world_packages.at package_name)
      case pkg of 
        Just (_,v) -> pure v
        Nothing -> throwError . lift_err . InternalErr $ "can't find package" <> pretty package_name

  -- Modify a package
  , set_package_imports = \package_name imports -> do
      mpkg <- use $ world_packages.at package_name
      case mpkg of
        Just (sem_package, package) ->
          -- TODO: re-evaluate package (requires source text...)
          let package' = ((package_header.requires) .~ imports) package
              sem_package' = sem_package { sprequires = imports}
          in world_packages.at package_name .= Just (sem_package', package')
        Nothing -> pure ()

  , set_package_exports = \package_name exports -> do
      mpkg <- use $ world_packages.at package_name
      case mpkg of
          -- TODO: re-evaluate package (requires source text for proper name resolution?)
        Just (sem_package, package) -> 
          let package' = ((package_header.requires) .~ exports) package
              sem_package' = sem_package { spprovides = exports}
          in world_packages.at package_name .= Just (sem_package', package')
        Nothing -> pure ()


  -- TODO: need to update properly if other modules depend on this one
  , intern_module = \(Path (package_name, module_name)) modul -> do
      packages <- use world_packages
      let sem_env = to_semenv $ CanonEnv packages Map.empty Map.empty
      pkg_pr <- case Map.lookup package_name packages of 
        Just (sem_package, package) -> do
          sem_module <- let ?lift_err = lift_err . EvalErr in eval_module sem_env modul
          let sem_package' = sem_package { spmodules = (insert_at_path module_name sem_module (spmodules sem_package)) }
              package' = (package_modules %~ (insert_at_path module_name modul)) package
          pure $ (sem_package', package')
        Nothing -> throwError $ lift_err $ InternalErr ("Couldn't find package:" <+> pretty package_name)
      (world_packages.at package_name) .= Just pkg_pr

  , get_env = canon_get_env lift_err <$> get
  , get_precs = \package_name imports -> do
      world <- get
      canon_get_precs lift_err world package_name imports
      
  , get_resolve = \package_name imports -> do
      world <- get
      canon_get_resolve lift_err world package_name imports
  
  , get_available_modules = \package_name -> do
      packages <- use world_packages
      case Map.lookup package_name packages of 
        Just (_, package) -> pure $ get_paths (package^.package_modules)
        Nothing -> throwError $ lift_err $ InternalErr ("couldn't find package:" <+> pretty package_name)

  , get_available_packages = do
      packages <- use world_packages
      pure $ Map.foldrWithKey (\k _ l -> (k: l)) [] packages

  , run = \s mon -> 
      pure $ case run_gen $ runExceptT $ runStateT (unCanonM mon) s of 
        Right (v,s) -> (Right v, s)
        Left err -> (Left err, s)

  , start_state = World Map.empty
  , stop = pure ()
  }
