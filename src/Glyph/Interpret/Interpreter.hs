module Glyph.Interpret.Interpreter
  ( Interpreter(..)
  , InbuiltType(..)
  , FunctionPragma(..)
  , ArithFun(..)
  , World(..)
  , Image(..) ) where


{--------------------------------- INTERPRETER ---------------------------------}
{- The interpreter datatype represents an interpreter backend. The 'canonical' -}
{- Backend is implemented as a tree-walking interpreter.                       -}
{-                                                                             -}
{- Interpreter backends may have different capabilities, notably:              -}
{- • FFI to various languages platforms, notably:                              -}
{-   • JVM, CLR, Native, Web                                                   -}
{- • System interaction                                                        -}
{- • System interaction                                                        -}
{-------------------------------------------------------------------------------}


import Data.Text (Text)
import Data.Map (Map)

import Glyph.Abstract.Environment
import Glyph.Abstract.Unify
import Glyph.Abstract.Substitution
import Glyph.Concrete.Internal



{---------------------------------- INTERFACE ----------------------------------}

data World a = World (Map Text (a, Maybe (World a)))

data Image a = Image (World a) (Restarts a)

type Restarts a = [IO a]
  
data Interpreter m = Interpreter
  -- Evaluating single terms 
  { eval :: Path Name -> InternalCore -> InternalCore -> m InternalCore
  , norm_eq :: Path Name -> InternalCore -> InternalCore -> InternalCore -> m Bool
  , solve_formula :: Path Name -> Formula InternalCore -> m (Substitution InternalCore) 

  -- Updating the environment 
  , intern_module :: Path Name -> InternalModule -> m ()
  , intern_def :: Path Name -> InternalDef -> m ()

  -- capabilities (is m a comonad??)
  , extract_io :: forall a. m a -> IO (a, m ())
  , extract_pure :: forall a. Maybe (m a -> (a, m ()))
  
  -- Interacting with the monad

  -- Producing/Loading an image 
  -- , from_image :: Image InternalCore -> IO (m ())  
  -- , to_image :: m () -> IO (Image InternalCore)
  }

data InbuiltType = InbuiltNat | InbuiltFloat | InbuiltSigned | InbuiltUnsigned | InbuiltChar 

data FunctionPragma = InbuiltArith   

data ArithFun = Add | Sub | Mul | Div
