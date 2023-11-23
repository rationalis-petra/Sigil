{-# OPTIONS_GHC -Wno-orphans #-}
module Sigil.Parse.Syntax
  ( Syntax(..)
  , SynModule(..)
  , SynEntry(..)
  , RawTel
  , MixToken(..)
  ) where

import Data.List (intersperse)
import Data.Text (Text)
import Data.Foldable

import Prettyprinter

import Sigil.Abstract.Names (Path(..))
import Sigil.Concrete.Decorations.Range
import Sigil.Abstract.Syntax
  (Pattern(..), ImportDef, ExportDef)

type RawTel = [(Maybe Text, Maybe (Syntax, Syntax, Syntax), Syntax)]

data MixToken s = NamePart Text | Syn s
  deriving Show

data Syntax
  = RMix Range [MixToken Syntax]
  | RUni Range Integer
  | RPrd Range (Maybe Text) (Maybe Syntax) Syntax
  | RAbs Range (Maybe Text) (Maybe Syntax) Syntax
  | REql Range RawTel Syntax Syntax Syntax
  | RDap Range RawTel Syntax
  | RInd Range Text (Maybe Syntax) [(Text, Syntax)]
  | RCtr Range Text (Maybe Syntax)
  | RRec Range (Maybe Text) (Maybe Syntax) Syntax [(Pattern Text, Syntax)]

data SynModule = RModule Path [ImportDef] [ExportDef] [SynEntry]

data SynEntry =
  RSingle Range Text (Maybe Syntax) Syntax

instance Functor MixToken where
  fmap f = \case 
    NamePart t -> NamePart t
    Syn x -> Syn $ f x

instance Eq (MixToken s) where  
  (NamePart p) == (NamePart p') = p == p'
  (Syn _) == (Syn _) = True -- s == s'
  _ == _ = False

instance Ord (MixToken s) where  
  compare (NamePart p) (NamePart p') = compare p p'
  compare (Syn _) (Syn _) = EQ -- compare s s'
  compare (Syn _) (NamePart _) = GT
  compare (NamePart _) (Syn _) = LT

instance Pretty s => Pretty (MixToken s) where
  pretty = \case
    NamePart p -> "(np" <+> pretty p <> ")"
    Syn s -> "(sy" <+> pretty s <> ")"

instance Pretty Syntax where
  pretty = \case 
    RMix _ toks -> "mix [" <> sep (map pretty toks) <> "]"
    RUni _ n -> "𝕌" <> pretty n
    RPrd _ mt ms body ->
      (case (mt, ms) of
         (Just t, Just v) -> "(" <> pretty t <+> "⮜" <+> pretty v <> ")"
         (Just t, Nothing) -> "(" <> pretty t <+> "⮜ _)"
         (Nothing, Just v) -> pretty v
         _ -> "_")
      <+> "→" <+> pretty body
    RAbs _ mt ms body -> "λ"
       <+> (case (mt, ms) of
              (Just t, Just v) -> "(" <> pretty t <+> "⮜" <+> pretty v <> ")"
              (Just t, Nothing) -> pretty t
              (Nothing, Just v) -> "(_ ⮜" <+> pretty v <> ")"
              _ -> "_")
      <+> "→" <+> pretty body
    REql _ tel ty v1 v2 -> "ι" <+> pretty_tel tel <+> pretty ty <+> pretty v1 <+> pretty v2
    RDap _ tel id -> "ρ" <+> pretty_tel tel <+> pretty id
    RInd _ name ms ctors ->
      vsep ["μ" <+> pretty name <> ","
                <+> maybe "." ((<> ".") . pretty) ms
           , indent 2 (align (vsep $ map (\(text, ty) -> pretty text <+> pretty ty) ctors))
           ] 
    RCtr _ label mty -> ":" <> pretty label <+> maybe "" (("﹨" <+>) . pretty) mty 
    RRec _ mt mty val cases ->
      vsep [ "φ" <+> maybe "_" pretty mt <> "⮜" <+> maybe "_" pretty mty <> "," <+> pretty val
           , indent 2 (align (vsep $ map pretty_case cases))
           ]
      where 
        pretty_case (pat, body) = pretty_pat pat <+> "→" <+> pretty body
        pretty_pat = \case 
          PatCtr n subpats -> pretty (":" <> n) <+> sep (map pbracket subpats)
          PatVar n -> pretty n
        pbracket p = case p of
          PatCtr _ _ -> "(" <> pretty_pat p <> ")"
          PatVar _ -> pretty_pat p

    where
      pretty_tel tel =
          case map pretty_tentry tel of
            (hd:tl) -> (align $ sep $ hd : zipWith (<+>) (repeat ",") tl) <> "."
            [] -> "."
      pretty_tentry (mt, mty, prf) = 
        maybe "_" pretty mt <+> "⮜" <+> maybe "_" pretty mty <+> "≜" <+> pretty prf

instance Pretty SynEntry where
  pretty (RSingle _ nm ms syn) = 
    case ms of
      Just ty ->
        vsep [ pretty nm <+> "⮜" <+> pretty ty
             , pretty nm <+> "≜" <+> pretty syn ]
      Nothing -> pretty nm <+> "≜" <+> pretty syn

instance Pretty SynModule where
  -- TODO: imports/exports
  pretty (RModule path _ _ entries) = 
    vsep $
    ("module" <+> (foldl' (<>) "" . zipWith (<>) ("" : repeat ".") . fmap pretty . toList . unPath $ path))
    : emptyDoc : intersperse emptyDoc (fmap (align . pretty) entries)

