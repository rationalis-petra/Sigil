module Glyph.Concrete.Typed
  ( Typed
  , TypedCore
  , TypedDefinition ) where


import Glyph.Abstract.Environment
import Glyph.Abstract.Syntax


data Typed

type instance Coreχ AnnBind Name Typed = ()
type instance Varχ Typed = ()
type instance Uniχ Typed = ()
type instance Prdχ Typed = ()
type instance Absχ Typed = ()
type instance Appχ Typed = ()

type TypedCore = Core AnnBind Name Typed

type TypedDefinition = Definition AnnBind Name Typed
  
