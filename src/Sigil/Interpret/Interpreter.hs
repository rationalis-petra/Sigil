module Sigil.Interpret.Interpreter
  ( Interpreter(..)
  , InbuiltType(..)
  , FunctionPragma(..)
  , ArithFun(..)
  , World(..)
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

import Prettyprinter.Render.Sigil

import Sigil.Abstract.Names
import Sigil.Abstract.Environment
import Sigil.Analysis.Typecheck
import Sigil.Abstract.Syntax (ImportDef)
import Sigil.Parse.Mixfix (Precedences)
import Sigil.Concrete.Internal


{---------------------------------- INTERFACE ----------------------------------}


data Image a = Image (World a) (Restarts a)

type Restarts a = [IO a]

-- m = monad
-- env = environment
-- s = state
-- t = term representation
data Interpreter m err env s t = Interpreter
  -- Converting to/from the term representation, 't'
  { reify :: InternalCore -> m t
  , reflect :: t -> m InternalCore

  -- Evaluate a term t in the environment e
  , eval :: (err -> err) -> env -> t -> t -> m t
  -- Return true if two terms are canonically equal, false otherwise 
  , norm_eq :: (err -> err) -> env -> t -> t -> t -> m Bool
  -- Higher Order Unification algorithm implementation
  -- , solve_formula :: e -> Formula t -> m (Substitution t)

  -- environment manipulation
  -- load a module into the interpreter's state
  , intern_module :: Path Text -> InternalModule -> m ()

  -- get the initial environment/precedences for a given module (path) with a
  -- set of imports
  , get_env :: Path Text -> [ImportDef] -> m env
  , get_precs :: Path Text -> [ImportDef] -> m Precedences

  -- The Monad m
  , run :: forall a. s -> m a -> IO (Either err a, s)

  -- Startup and close should be used for state s  
  , start_state :: s
  , stop :: m ()

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

