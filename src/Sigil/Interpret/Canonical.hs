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

import Control.Monad.State (StateT, modify, runStateT)
import Control.Monad.Except (ExceptT, runExceptT)
import qualified Data.Map as Map
--import Data.Text (Text)

--import Prettyprinter  
import Prettyprinter.Render.Sigil

import Sigil.Parse.Mixfix
import Sigil.Abstract.Environment
import Sigil.Concrete.Internal
import Sigil.Interpret.Interpreter
--import Sigil.Interpret.Unify
import Sigil.Interpret.Term

newtype Context = Context { world :: World InternalModule } -- threads :: ??
  
type CanonM = StateT (World InternalModule) (ExceptT SigilDoc Gen)

canonical_interpreter :: Environment Name e => Interpreter CanonM (e (Maybe InternalCore, InternalCore)) (World InternalModule) InternalCore
canonical_interpreter = Interpreter
  -- reify_term :: e -> InternalCore -> m t
  { reify = pure
  , reflect = pure
  -- , reflect_term :: t -> m InternalCore


  -- eval :: Path Name -> InternalCore -> InternalCore -> m InternalCore
  , eval = \env ty term -> do
      normalize env ty term

  -- norm_eq :: Path Name -> InternalCore -> InternalCore -> InternalCore -> m Bool
  , norm_eq = \env ty a b -> do
      equiv env ty a b

  -- solve :: Path Name -> Formula InternalCore -> m (Substitution InternalCore) 
  --, solve_formula = \_ formula -> do
      -- TODO: solve needs to depend on path!
      -- env <- build_eval_env_from path
      -- solve formula

  -- Updating the environment 
  -- intern_module :: Path Name -> InternalModule -> m ()
  , intern_module = \path modul ->
      modify (insert_at_path path modul)

  -- get_env :: Path Text -> [ImportDef] -> m e
  , get_env = \_ _ -> pure env_empty

  , get_precs = \_ _ ->
      pure $ Precedences Map.empty "in" "pre" "post" "close"

  -- capabilities (is m a comonad??)
  -- extract_io :: forall a. m a -> IO (a, m ())
  -- run :: forall a. s -> m a -> IO (Either SigilDoc a, s)
  , run = \s mon -> 
      pure $ case run_gen $ runExceptT $ runStateT mon s of 
        Right (v,s) -> (Right v, s)
        Left err -> (Left err, s)

  , start_state = World Map.empty
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

