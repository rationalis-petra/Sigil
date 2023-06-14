module Glyph.Concrete.Parsed
  ( Parsed
  , ParsedCore
  , ParsedDef
  , PUnit(..)
  , range
  , pattern Core
  , pattern Uni
  , pattern Var
  , pattern Prd
  , pattern Abs
  , pattern App
  ) where


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

type ParsedCore = Core OptBind Text Parsed

type instance Mutualχ Parsed = Range
type instance SigDefχ Parsed = Range
type instance IndDefχ Parsed = Range

type ParsedDef = Definition OptBind Text Parsed

{-# COMPLETE Core, Uni, Var, Prd, Abs, App #-}
pattern Core :: ParsedCore
pattern Core <- Coreχ _
  where Core = Coreχ PUnit
  
pattern Uni :: Range -> Int -> ParsedCore
pattern Uni r n <- Uniχ r n
  where Uni r n = Uniχ r n

pattern Var :: Range -> Text -> ParsedCore
pattern Var r n <- Varχ r n
  where Var r n = Varχ r n

pattern Prd :: Range -> OptBind Text ParsedCore -> ParsedCore -> ParsedCore
pattern Prd r b e <- Prdχ r b e
  where Prd r b e = Prdχ r b e

pattern Abs :: Range -> OptBind Text ParsedCore -> ParsedCore -> ParsedCore
pattern Abs r b e <- Absχ r b e
  where Abs r b e = Absχ r b e

pattern App :: Range -> ParsedCore -> ParsedCore -> ParsedCore
pattern App r a b <- Appχ r a b
  where App r a b = Appχ r a b

range :: ParsedCore -> Range
range core = case core of
  Core -> mempty
  Uni r _ -> r
  Var r _ -> r
  Prd r _ _ -> r
  Abs r _ _ -> r
  App r _ _ -> r

  
{---------------------------------- INSTANCES ----------------------------------}


instance Pretty ParsedCore where
  pretty =
    pretty_core_builder pretty pretty pretty
  
instance Pretty ParsedDef where
  pretty =
    pretty_def_builder pretty pretty pretty
