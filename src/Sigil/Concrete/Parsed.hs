module Sigil.Concrete.Parsed
  ( Parsed
  , ParsedCore
  , ParsedEntry
  , ParsedModule
  , pattern Rat
  , pattern Uni
  , pattern Var
  , pattern Prd
  , pattern Abs
  , pattern App
  , pattern Ind
  , pattern Ctr
  , pattern Rec
  , pattern Eql
  , pattern ETC
  , pattern CTE
  , pattern Dap
  , pattern TrL
  , pattern TrR
  , pattern LfL
  , pattern LfR
  ) where

{----------------------------------- PARSED ------------------------------------}
{- The Parsed Type describes s the creation and manipulation of abstract Sigil.-}
{- terms, i.e. the core calculus. This includes:                               -}
{- • Representation of Sigil. Terms and Environments                           -}
{- • Normalization                                                             -}
{- • Substitution                                                              -}
{- • Higher Order Unification                                                  -}
{- • Type Checking & Type Inference                                            -}
{-                                                                             -}
{-------------------------------------------------------------------------------}

import Data.Text

import Prettyprinter

import Sigil.Abstract.Names
import Sigil.Abstract.Syntax
import Sigil.Concrete.Decorations.Range
import Sigil.Concrete.Decorations.Implicit
import Sigil.Concrete.Decorations.Rational

data Parsed
type instance Functorχ Parsed = Maybe
type instance Coreχ OptBind Text Parsed = PRational
type instance Varχ Parsed = Range
type instance Uniχ Parsed = Range
type instance Prdχ Parsed = (Range, ArgType)
type instance Absχ Parsed = (Range, ArgType)
type instance Appχ Parsed = (Range, ArgType)
type instance Indχ Parsed = Range
type instance Ctrχ Parsed = Range
type instance Recχ Parsed = Range
type instance Eqlχ Parsed = Range
type instance ETCχ Parsed = Range
type instance CTEχ Parsed = Range
type instance Dapχ Parsed = Range
type instance TrLχ Parsed = Range
type instance TrRχ Parsed = Range
type instance LfLχ Parsed = Range
type instance LfRχ Parsed = Range

type ParsedCore = Core OptBind Text Parsed

type instance Singleχ Parsed = Range

type ParsedEntry = Entry OptBind Text Parsed

type ParsedModule = Module OptBind Text Parsed

{-# COMPLETE Uni, Var, Prd, Abs, App, Ind, Ctr, Rec
 , Eql, ETC, CTE, Dap, TrL, TrR, LfL, LfR
 , Rat #-}
pattern Uni :: Range -> Integer -> ParsedCore
pattern Uni r n <- Uniχ r n
  where Uni r n = Uniχ r n

pattern Var :: Range -> Text -> ParsedCore
pattern Var r n <- Varχ r n
  where Var r n = Varχ r n

pattern Prd :: Range -> ArgType -> OptBind Text ParsedCore -> ParsedCore -> ParsedCore
pattern Prd r ty b e <- Prdχ (r,ty) b e
  where Prd r ty b e = Prdχ (r,ty) b e

pattern Abs :: Range -> ArgType -> OptBind Text ParsedCore -> ParsedCore -> ParsedCore
pattern Abs r ty b e <- Absχ (r,ty) b e
  where Abs r ty b e = Absχ (r,ty) b e

pattern App :: Range -> ArgType -> ParsedCore -> ParsedCore -> ParsedCore
pattern App r t a b <- Appχ (r,t) a b
  where App r t a b = Appχ (r,t) a b

pattern Ind :: Range -> Text -> Maybe ParsedCore -> [(Text, ParsedCore)] -> ParsedCore
pattern Ind r name msort ctors <- Indχ r name msort ctors
  where Ind r name msort ctors = Indχ r name msort ctors

pattern Ctr :: Range -> Text -> Maybe ParsedCore -> ParsedCore
pattern Ctr r label ty <- Ctrχ r label ty 
  where Ctr r label ty = Ctrχ r label ty 
  
pattern Rec :: Range -> (OptBind Text ParsedCore) -> ParsedCore -> [(Case OptBind Text Parsed)] -> ParsedCore
pattern Rec r rec val cases <- Recχ r rec val cases
  where Rec r rec val cases = Recχ r rec val cases

pattern Eql :: Range -> (Tel OptBind Text ParsedCore) -> ParsedCore -> ParsedCore -> ParsedCore -> ParsedCore
pattern Eql r tel ty a a' <- Eqlχ r tel ty a a'
  where Eql r tel ty a a' = Eqlχ r tel ty a a'

pattern ETC :: Range -> ParsedCore -> ParsedCore
pattern ETC r val <- ETCχ r val
  where ETC r val = ETCχ r val

pattern CTE :: Range -> ParsedCore -> ParsedCore
pattern CTE r val <- CTEχ r val
  where CTE r val = CTEχ r val

pattern Dap :: Range -> (Tel OptBind Text ParsedCore) -> ParsedCore -> ParsedCore
pattern Dap r tel val <- Dapχ r tel val
  where Dap r tel val = Dapχ r tel val

pattern TrL :: Range -> (Tel OptBind Text ParsedCore) -> ParsedCore -> ParsedCore -> ParsedCore
pattern TrL r tel ty val <- TrLχ r tel ty val
  where TrL r tel ty val = TrLχ r tel ty val

pattern TrR :: Range -> (Tel OptBind Text ParsedCore) -> ParsedCore -> ParsedCore -> ParsedCore
pattern TrR r tel ty val <- TrRχ r tel ty val
  where TrR r tel ty val = TrRχ r tel ty val

pattern LfL :: Range -> (Tel OptBind Text ParsedCore) -> ParsedCore -> ParsedCore -> ParsedCore
pattern LfL r tel ty val <- LfLχ r tel ty val
  where LfL r tel ty val = LfLχ r tel ty val

pattern LfR :: Range -> (Tel OptBind Text ParsedCore) -> ParsedCore -> ParsedCore -> ParsedCore
pattern LfR r tel ty val <- LfRχ r tel ty val
  where LfR r tel ty val = LfRχ r tel ty val

pattern Rat :: Range -> Rational -> ParsedCore  
pattern Rat r n <- Coreχ (PRational r n)
  where Rat r n = Coreχ (PRational r n)

instance HasRange ParsedCore where
  range core = case core of
    Rat r _ -> r
    Uni r _ -> r
    Var r _ -> r
    Prd r _ _ _ -> r
    Abs r _ _ _ -> r
    App r _ _ _ -> r
    Ind r _ _ _ -> r
    Ctr r _ _ -> r
    Rec r _ _ _ -> r
    Eql r _ _ _ _ -> r
    ETC r _ -> r
    CTE r _ -> r
    Dap r _ _ -> r
    TrL r _ _ _ -> r
    TrR r _ _ _-> r
    LfL r _ _ _-> r
    LfR r _ _ _ -> r

  
{---------------------------------- INSTANCES ----------------------------------}


instance Pretty ParsedCore where
  pretty =
    pretty_core_builder pretty pretty
  
instance Pretty ParsedEntry where
  pretty =
    pretty_entry_builder name pretty pretty pretty

instance Pretty ParsedModule where
  pretty =
    pretty_mod_builder pretty

instance Show ParsedCore where
  show = show . pretty
