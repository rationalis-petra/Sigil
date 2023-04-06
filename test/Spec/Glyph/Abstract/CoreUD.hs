module Spec.Glyph.Abstract.CoreUD (UD, void) where

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

instance Eq Void where  
  _ == _ = True

instance AlphaEq Name Void where  
  αequal _ _ _ = True

instance Pretty Void where  
  pretty _ = ""
