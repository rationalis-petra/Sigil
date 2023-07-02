module Glyph.Interpret.Canonical
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

import Control.Monad.State (StateT)
import Control.Monad.Except (ExceptT)
import Data.Text (Text)

import Prettyprinter  
import Prettyprinter.Render.Glyph

import Glyph.Abstract.Environment
import Glyph.Concrete.Internal
import Glyph.Interpret.Interpreter
import Glyph.Interpret.Unify
import Glyph.Interpret.Term

data Context = Context { world :: World InternalCore } -- threads :: ??
  
type CanonM = StateT (World InternalCore) (ExceptT (Doc GlyphDoc) Gen)

canonical_interpreter :: Interpreter CanonM 
canonical_interpreter = Interpreter
  -- eval :: Path Name -> InternalCore -> InternalCore -> m InternalCore
  -- evaluation
  { eval = \path ty term -> do
      env <- build_eval_env_from path
      normalize env ty term

  -- norm_eq :: Path Name -> InternalCore -> InternalCore -> InternalCore -> m Bool
  , norm_eq = \path ty a b -> do
      env <- build_eval_env_from path
      equiv env ty a b

  -- solve :: Path Name -> Formula InternalCore -> m (Substitution InternalCore) 
  , solve_formula = \_ formula -> do
      -- TODO: solve neets to depend on path!
      -- env <- build_eval_env_from path
      solve formula

  -- Updating the environment 
  -- intern_module :: Path Name -> InternalModule -> m ()
  , intern_module = error "intern_module not implemented"
  -- , intern_module path text = do
  --     ctx <- context_from_path path
  --     parsed_modul <- parseToErr (mod (ctx^.parser_env) <* eof) "interpreter-in" text
  --     resolved_module <- resolve parsed_module
  --     checked_module <- typecheck_module resolved_modul 
  --     update_world_with_module checked_module

  -- capabilities (is m a comonad??)
  -- extract_io :: forall a. m a -> IO (a, m ())
  , extract_io = error "extract_io not implemented"
  -- extract_pure :: forall a. Maybe (m a -> (a, m ()))
  , extract_pure = error "extract_pure not implemented"

  }




build_eval_env_from :: Path Text -> CanonM (Env (Maybe InternalCore, InternalCore))
build_eval_env_from = error "build_eval_env"
 -- build_eval_env_from path = do
 --  menv <- get_module_env path <$> get
 --  case menv of 
 --    Just modul -> env
 --    Nothing ->
 --      throwError ("Can't find module at path" <+> pretty path)

