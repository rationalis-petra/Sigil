module Sigil.Concrete.Decorations.Implicit
  ( ArgType(..)
  ) where

import Prettyprinter

data ArgType = Implicit | Regular -- will add | Typeclass  
  deriving (Eq, Ord, Show)

instance Pretty ArgType where
  pretty = \case
    Regular -> "expl"
    Implicit -> "impl"
