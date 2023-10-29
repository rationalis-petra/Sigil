{-# OPTIONS_GHC -Wno-unrecognised-pragmas #-}
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
import qualified Data.Map as Map
import qualified Data.Set as Set

import Control.Lens (makeLenses, (^.), (%=), use)
import Prettyprinter

import Sigil.Abstract.Syntax
import Sigil.Abstract.Environment
import Sigil.Parse.Mixfix
import Sigil.Concrete.Internal
import Sigil.Interpret.Interpreter
import Sigil.Interpret.Term

-- the type of module. Contains both
-- a regular 'internal' module 
-- a 'semantic' module, i.e. a pre-evaluated module


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
 

canonical_interpreter :: Environment Name e => (InterpreterErr -> err)
  -> Interpreter (CanonM err) err (e (Maybe InternalCore, InternalCore)) Context InternalCore
canonical_interpreter liftErr = Interpreter
  { reify = pure
  , reflect = pure

  , eval = \f env ty term -> do
      normalize (f . liftErr . EvalErr) env ty term

  , norm_eq = \f env ty a b -> do
      equiv (f . liftErr . EvalErr) env ty a b

  , intern_module = \path modul ->
      world %= insert_at_path path modul

  , get_env = \_ _ -> pure env_empty

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

  , run = \s mon -> 
      pure $ case run_gen $ runExceptT $ runStateT mon s of 
        Right (v,s) -> (Right v, s)
        Left err -> (Left err, s)

  , start_state = Context (World Map.empty)
  , stop = pure ()

  , to_image = error "to_image not implemented"
  , from_image = error "to_image not implemented"
  }




-- build_eval_env_from :: Environment Name e => Path Text -> CanonM (e (Maybe InternalCore, InternalCore))
-- build_eval_env_from = error "build_eval_env"
 -- build_eval_env_from path = do
 --  menv <- get_module_env path <$> get
 --  case menv of 
 --    Just modul -> env
 --    Nothing ->
 --      throwError ("Can't find module at path" <+> pretty path)

