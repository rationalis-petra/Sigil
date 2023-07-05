module Glyph.Concrete.Resolved
  ( Resolved
  , ResolvedCore
  , ResolvedDef
  , ResolvedModule
  ) where


import Prettyprinter

import Glyph.Abstract.Environment
import Glyph.Abstract.Syntax
import Glyph.Concrete.Decorations.Range


data Resolved
type instance Coreχ OptBind Name Resolved = ()
type instance Varχ Resolved = Range
type instance Uniχ Resolved = Range
type instance Prdχ Resolved = Range
type instance Absχ Resolved = Range
type instance Appχ Resolved = Range

type ResolvedCore = Core OptBind Name Resolved

type instance Mutualχ Resolved = Range

type ResolvedDef = Definition OptBind Name Resolved
  
--type instance Appχ Resolved = Range
type ResolvedModule = Module OptBind Name Resolved

instance Pretty ResolvedCore where
  pretty = pretty_core_builder pretty pretty pretty 
