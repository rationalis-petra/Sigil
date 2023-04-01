module Glyph.Abstract.Typecheck
  () where


{-------------------------------- TYPECHECKING ---------------------------------}
{- Typechecking is heavily reliant on Unification, and in fact can be seen as  -}
{- a specialized form of the unification problem (see Glyph.Abstract.Unify).   -}
{-                                                                             -}
{- Therefore, the function contained here is largely an adapter - it takes in  -}
{- a term and transforms it into a form amenable to unification, runs the      -}
{- unifier and interprets the result.                                          -}
{-------------------------------------------------------------------------------}


-- import Control.Monad.Except (MonadError)
-- import qualified Data.Map as Map
-- import Data.Map (Map)  

-- import Prettyprinter

-- import Glyph.Abstract.Term  
-- import Glyph.Abstract.Unify  
