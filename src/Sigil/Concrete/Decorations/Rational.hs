module Sigil.Concrete.Decorations.Rational (PRational(..)) where

import Data.Text

import Prettyprinter

import Sigil.Abstract.AlphaEq
import Sigil.Concrete.Decorations.Range

data PRational = PRational Range Rational

instance AlphaEq Text PRational where   
  αequal _ (PRational _ r) (PRational _ r') = r == r'

instance Pretty PRational where   
  pretty (PRational _ r) = pretty $ show r
