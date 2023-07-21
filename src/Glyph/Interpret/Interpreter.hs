module Glyph.Interpret.Interpreter
  ( Interpreter(..)
  , InbuiltType(..)
  , FunctionPragma(..)
  , ArithFun(..)
  , World(..)
  , insert_at_path
  , Image(..) ) where


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
import qualified Data.Map as Map
import Data.Map (Map)
import Data.List.NonEmpty

import Prettyprinter.Render.Glyph (GlyphDoc)  

import Glyph.Abstract.Environment
--import Glyph.Abstract.Unify
--import Glyph.Abstract.Substitution
import Glyph.Concrete.Internal


{---------------------------------- INTERFACE ----------------------------------}

newtype World a = World (Map Text (Maybe a, Maybe (World a)))

insert_at_path :: Path Text -> a -> World a -> World a
insert_at_path path a (World subtree) =
  case path of 
    (p :| []) -> case Map.lookup p subtree of 
      Just (_, v) -> World $ Map.insert p (Just a, v) subtree
      Nothing -> World $ Map.insert p (Just a, Nothing) subtree

    (p :| (t:ts)) -> case Map.lookup p subtree of 
      Just (v, Just subworld) -> World $ Map.insert p (v, Just subworld') subtree
        where
          subworld' = insert_at_path (t :| ts) a subworld
      Just (v, Nothing) -> World $ Map.insert p (v, Just subworld) subtree
        where 
          subworld = insert_at_path (t :| ts) a (World $ Map.empty)
      Nothing -> World $ Map.insert p (Nothing, Just subworld) subtree
        where 
          subworld = insert_at_path (t :| ts) a (World $ Map.empty)

data Image a = Image (World a) (Restarts a)

type Restarts a = [IO a]

-- m = monad
-- e = environment
-- s = state
-- t = term representation
data Interpreter m e s t = Interpreter
  -- Converting to/from the term representation, 't'
  { reify :: InternalCore -> m t
  , reflect :: t -> m InternalCore

  -- Evaluate a term t in the environment e
  , eval :: e -> t -> t -> m t
  -- Return true if two terms are canonically equal, false otherwise 
  , norm_eq :: e -> t -> t -> t -> m Bool
  -- Higher Order Unification algorithm implementation
  -- , solve_formula :: e -> Formula t -> m (Substitution t)

  -- environment manipulation
  -- load a module into the interpreter's state
  , intern_module :: Path Text -> InternalModule -> m ()
  , get_env :: Maybe (Path Text) -> m e

  -- The Monad m
  , run :: forall a. s -> m a -> IO (Either GlyphDoc a, s)

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

-- lookup_path :: Path Name -> World -> Module Env
-- lookup_path path world = 

-- get_path_env :: Path Text -> World a -> Env (Maybe a, a)
-- get_path_env (name :| names) world =
--   case (lookup name world, names)  of 
--     (Just (), (x:xs))
--     (Just (), _)
--     (Nothing, _)
