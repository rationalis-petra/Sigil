module Sigil.Interpret.Interpreter
  ( Interpreter(..)
  , InbuiltType(..)
  , FunctionPragma(..)
  , ArithFun(..)
  , InterpreterErr(..)
  , Image(..)
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

import Prettyprinter.Render.Sigil

import Sigil.Abstract.Names
import Sigil.Abstract.Unify
import Sigil.Abstract.Substitution
import Sigil.Abstract.Syntax (ImportDef, MTree)
import Sigil.Analysis.Typecheck
import Sigil.Parse.Mixfix (Precedences)
import Sigil.Concrete.Internal


{---------------------------------- INTERFACE ----------------------------------}


data Image a = Image (MTree a) (Restarts a)

type Restarts a = [IO a]

-- m = monad
-- env = environment
-- s = state
-- t = term representation
data Interpreter m err env s t f = Interpreter
  -- Converting to/from the term representation, 't'
  { reify :: InternalCore -> m t
  , reflect :: t -> m InternalCore

  , reify_formula :: Formula Name InternalCore -> m f
  , reflect_formula :: f -> m (Formula Name InternalCore)

  {--------------------- Term Queries and Transformations ----------------------}
  -- Evaluate a term t in the environment e
  , eval :: (err -> err) -> env -> t -> t -> m t
  -- Return true if two terms are canonically equal, false otherwise 
  , norm_eq :: (err -> err) -> env -> t -> t -> t -> m Bool
  -- Higher Order Unification algorithm implementation
  , solve_formula :: (err -> err) -> env -> f -> m (Substitution Name t)

  {------------------------- Environment Manipulation --------------------------}
  -- Load a module into the interpreter's state
  , intern_module :: Text -> Path -> InternalModule -> m ()
  , intern_package :: Text -> InternalPackage -> m ()

  {---------------------------- Environment Queries ----------------------------}
  -- Get the initial environment/precedences for a given package with a
  -- set of imports.
  , get_env :: Text -> [ImportDef] -> m env
  , get_precs :: Text -> [ImportDef] -> m Precedences
  , get_resolve :: Text -> [ImportDef] -> m (Map Text QualName)

  -- As above, but in the context of a specific module, rather than a package + imports.
  , get_module_env :: Text -> Path -> m env
  , get_module_precs :: Text -> Path -> m Precedences
  , get_module_resolve :: Text -> Path -> m (Map Text QualName)

  -- Get all module paths in a package (does not include imported modules)
  , get_available_modules :: Text -> m [Path]
  , get_available_packages :: m [Text]

  {------------------------------ Using the Monad ------------------------------}
  -- The Monad m
  , run :: forall a. s -> m a -> IO (Either err a, s)

  -- Startup and close should be used for state s  
  , start_state :: s
  , stop :: m ()

  {---------------------------------- Images -----------------------------------}
  -- Producing/Loading an image 
  , from_image :: Image InternalCore -> m ()
  , to_image :: m (Image InternalCore)
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

