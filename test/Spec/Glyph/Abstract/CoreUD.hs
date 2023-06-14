module Spec.Glyph.Abstract.CoreUD
  ( CoreUD
  , DefinitionUD
  , UD
  , void ) where

import Prettyprinter

import Glyph.Abstract.Syntax
import Glyph.Abstract.Environment
import Glyph.Abstract.AlphaEq

-- undecorated tree  
data Void
data UD

void :: Void  
void = error "attempt to evaluate void"

type instance Coreχ OptBind Name UD = Void
type instance Uniχ UD = Void
type instance Varχ UD = Void
type instance Prdχ UD = Void
type instance Absχ UD = Void
type instance Appχ UD = Void
type instance Mutualχ UD = Void

type CoreUD = Core OptBind Name UD
type DefinitionUD = Definition OptBind Name UD

instance Eq Void where  
  _ == _ = True

instance AlphaEq Name Void where  
  αequal _ _ _ = True

instance Pretty Void where  
  pretty _ = ""

instance Pretty CoreUD where
  pretty = pretty_core_builder pretty pretty pretty
