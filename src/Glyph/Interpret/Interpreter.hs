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

newtype World a = World (Map Text (a, Maybe (World a)))

data Image a = Image (World a) (Restarts a)

type Restarts a = [IO a]
  
data Interpreter m = Interpreter
  -- Evaluating single terms 
  { eval :: Path Text -> InternalCore -> InternalCore -> m InternalCore
  , norm_eq :: Path Text -> InternalCore -> InternalCore -> InternalCore -> m Bool
  , solve_formula :: Path Text -> Formula InternalCore -> m (Substitution InternalCore) 

  -- Updating the environment 
  , intern_module :: Path Text -> Text -> m ()

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


-- lookup_path :: Path Name -> World -> Module Env
-- lookup_path path world = 

-- get_path_env :: Path Text -> World a -> Env (Maybe a, a)
-- get_path_env (name :| names) world =
--   case (lookup name world, names)  of 
--     (Just (), (x:xs))
--     (Just (), _)
--     (Nothing, _)
