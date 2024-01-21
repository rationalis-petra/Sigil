module Sigil.Interpret.Interpreter
  ( Interpreter(..)
  , InbuiltType(..)
  , FunctionPragma(..)
  , ArithFun(..)
  , InterpreterErr(..)
  ) where


{--------------------------------- INTERPRETER ---------------------------------}
{- The interpreter datatype represents an interpreter backend. The intent is   -}
{- to have algorithms which require term evaluation to be dependent on an      -}
{- interpreter. We can then swap out interpreters at runtime.                  -}
{- Backend is implemented as a tree-walking interpreter.                       -}
{-                                                                             -}
{- Interpreter backends may have different capabilities, notably:              -}
{- • FFI to various languages platforms, e.g.:                                 -}
{-   • JVM, CLR, Native, Web                                                   -}
{- • System interaction (console in/out etc.)                                  -}
{- • Program introspection                                                     -}
{-------------------------------------------------------------------------------}


import Data.Text (Text)
import Data.Map (Map)
import Data.List.NonEmpty (NonEmpty)

import Prettyprinter.Render.Sigil

import Sigil.Abstract.Names
import Sigil.Abstract.Unify
import Sigil.Abstract.Substitution
import Sigil.Abstract.Environment
import Sigil.Abstract.Syntax (ImportDef)
import Sigil.Analysis.Typecheck
import Sigil.Parse.Mixfix (Precedences)
import Sigil.Concrete.Internal


{---------------------------------- INTERFACE ----------------------------------}


-- m = monad
-- err = error type
-- env = environment 
-- s = state
data Interpreter m err env s = Interpreter
  {--------------------- Term Queries and Transformations ----------------------}
  -- Evaluate a term t in the environment e
  { eval :: (err -> err) -> env -> InternalCore -> InternalCore -> m InternalCore
  -- norm :: 
  -- Return true if two terms are canonically equal, false otherwise 
  , norm_eq :: (err -> err) -> env -> InternalCore -> InternalCore -> InternalCore -> m Bool
  -- Higher Order Unification algorithm implementation
  , solve_formula :: (err -> err) -> env -> (Formula Name InternalCore) -> m (Substitution Name InternalCore)

  {------------------------- Environment Manipulation --------------------------}
  -- Create or get a package
  , make_package :: Text -> m ()
  , intern_package :: Text -> InternalPackage -> m ()
  , get_package :: Text -> m InternalPackage

  -- Modify a package
  , set_package_imports :: Text -> [Text] -> m ()
  , set_package_exports :: Text -> [Text] -> m ()
  , intern_module :: Path -> InternalModule -> m ()

  {---------------------------- Environment Queries ----------------------------}
  -- , env_lookup :: Name -> env -> m (Maybe InternalCore, InternalCore)
  -- , env_insert :: Name -> (Maybe InternalCore, InternalCore) -> env -> m env
  
  -- Get the initial environment/precedences for a given package with a
  -- set of imports.
  , get_env :: m (Env env m)
  , get_precs :: Text -> [ImportDef] -> m Precedences
  , get_resolve :: Text -> [ImportDef] -> m (Map Text Path)

  -- This function is for use when typechecking a modules in an incomplete package
  -- , get_partial_env :: m env

  -- Get all packages, get all module paths in a package (does not include imported modules)
  , get_available_packages :: m [Text]
  , get_available_modules :: Text -> m [NonEmpty Text]

  {------------------------------ Using the Monad ------------------------------}
  -- The Monad m
  , run :: forall a. s -> m a -> IO (Either err a, s)

  -- Startup and close should be used for state s  
  , start_state :: s
  , stop :: m ()
  }

data InbuiltType = InbuiltNat | InbuiltFloat | InbuiltSigned | InbuiltUnsigned | InbuiltChar 

data FunctionPragma = InbuiltArith   

data ArithFun = Add | Sub | Mul | Div

data InterpreterErr
  = EvalErr SigilDoc
  | TCErr TCErr 
  | InternalErr SigilDoc 

instance SigilPretty InterpreterErr where
  spretty (EvalErr doc) = doc
  spretty (TCErr err) = spretty err
  spretty (InternalErr doc) = doc 

