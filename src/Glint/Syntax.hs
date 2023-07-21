module Glint.Syntax (GlnRaw(..)) where

import Data.Text (Text)

import Prettyprinter

data GlnRaw
  = Node Text [Text] [(Text, Text)] [Either GlnRaw Text]
  deriving (Ord, Eq)

instance Pretty GlnRaw where
  pretty (Node name args kwargs body) =
    "[" <> pretty name <+> (sep . map pretty $ args)
    <> (if (not (null kwargs)) then "," <> (sep . map pretty $ kwargs) else "")
    <> "|" <> sep (map (either pretty pretty) body) <> "]"
