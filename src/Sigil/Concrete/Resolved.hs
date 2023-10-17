module Sigil.Concrete.Resolved
  ( Resolved
  , ResolvedCore
  , ResolvedEntry
  , ResolvedModule
  ) where


import Prettyprinter

import Sigil.Abstract.Environment
import Sigil.Abstract.Syntax
import Sigil.Concrete.Decorations.Range


data Resolved
type instance Coreχ OptBind Name Resolved = ()
type instance Varχ Resolved = Range
type instance Uniχ Resolved = Range
type instance Prdχ Resolved = Range
type instance Absχ Resolved = Range
type instance Appχ Resolved = Range
type instance Eqlχ Resolved = Range
type instance Dapχ Resolved = Range
type instance Indχ Resolved = Range
type instance Ctrχ Resolved = Range
type instance Recχ Resolved = Range

type ResolvedCore = Core OptBind Name Resolved

type instance Mutualχ Resolved = Range
type instance Singleχ Resolved = Range

type ResolvedEntry = Entry OptBind Name Resolved
  
--type instance Appχ Resolved = Range
type ResolvedModule = Module OptBind Name Resolved

instance Pretty ResolvedCore where
  pretty = pretty_core_builder pretty pretty 

instance HasRange ResolvedCore where
  range core = case core of
    Coreχ _ -> mempty
    Uniχ r _ -> r
    Varχ r _ -> r
    Prdχ r _ _ -> r
    Absχ r _ _ -> r
    Appχ r _ _ -> r
    Eqlχ r _ _ _ _ -> r
    Dapχ r _ _ -> r
    Indχ r _ _ -> r
    Ctrχ r _ _ -> r
    Recχ r _ _ _ -> r
