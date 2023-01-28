module Spec.Glyph.CoreUD (UD, void) where

import Data.Void

import Glyph.Core

-- undecorated tree  
data UD

void :: Void  
void = error "attempt to evaluate void"

type instance Coreχ UD = Void
type instance Varχ UD = Void
type instance Prdχ UD = Void
type instance Absχ UD = Void
type instance Appχ UD = Void
