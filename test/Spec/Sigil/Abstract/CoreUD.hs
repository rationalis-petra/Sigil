module Spec.Sigil.Abstract.CoreUD
  ( CoreUD
  , EntryUD
  , ModuleUD
  , UD
  , void ) where

import Prettyprinter

import Sigil.Abstract.Names
import Sigil.Abstract.Syntax
import Sigil.Abstract.AlphaEq

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
type instance Eqlχ UD = Void
type instance Dapχ UD = Void
type instance Singleχ UD = Void

type CoreUD = Core OptBind Name UD
type EntryUD = Entry OptBind Name UD
type ModuleUD = Module OptBind Name UD

instance Eq Void where  
  _ == _ = True

instance AlphaEq Name Void where  
  αequal _ _ _ = True

instance Pretty Void where  
  pretty _ = ""

instance Pretty CoreUD where
  pretty = pretty_core_builder pretty pretty
