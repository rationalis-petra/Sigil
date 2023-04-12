module Glyph.Concrete.Parsed
  ( Parsed
  , RawCore
  , RawDefinition
  , PUnit(..)
  , range ) where


import Data.Text

import Prettyprinter

import Glyph.Abstract.Environment
import Glyph.Abstract.Syntax
import Glyph.Abstract.AlphaEq
import Glyph.Concrete.Decorations.Range

data PUnit = PUnit

instance AlphaEq Text PUnit where   
  αequal _ PUnit PUnit = True

instance Pretty PUnit where   
  pretty PUnit = ""

data Parsed
type instance Coreχ OptBind Text Parsed = PUnit
type instance Varχ Parsed = Range
type instance Uniχ Parsed = Range
type instance Prdχ Parsed = Range
type instance Absχ Parsed = Range
type instance Appχ Parsed = Range

type RawCore = Core OptBind Text Parsed

type RawDefinition = Definition OptBind Text Parsed
  
range :: Core b n Parsed -> Range
range (Coreχ _) = mempty
range (Uni r _) = r
range (Var r _) = r
range (Prd r _ _) = r
range (Abs r _ _) = r
range (App r _ _) = r
