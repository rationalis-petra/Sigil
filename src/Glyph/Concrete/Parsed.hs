module Glyph.Concrete.Parsed
  ( Parsed
  , RawCore
  , RawDefinition
  , range ) where


import Data.Text

import Glyph.Abstract.Environment
import Glyph.Abstract.Syntax
import Glyph.Concrete.Decorations.Range


data Parsed
type instance Coreχ Parsed = ()
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
