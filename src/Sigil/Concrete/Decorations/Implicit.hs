module Sigil.Concrete.Decorations.Implicit
  ( ArgType(..)
  ) where

data ArgType = Implicit | Regular -- will add | Typeclass  
  deriving (Eq, Ord, Show)
