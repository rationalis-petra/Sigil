module Glyph.Concrete.Resolved
  ( Resolved
  , ResolvedCore
  , ResolvedDefinition ) where


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

type ResolvedDefinition = Definition OptBind Name Resolved
  
