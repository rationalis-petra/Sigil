module Glyph.Name (
  QualName,
  Name(..)) where

import Prelude hiding (head)
import Data.Vector (Vector, head)
import Data.Text (Text, unpack)

import Prettyprinter  


{------------------------------------ NAMES ------------------------------------}
{- The Name type is used throughout the codebase, and represents names after   -}
{- Name resolution. A name is either:                                          -}
{- • A local variable, which uses a DeBruijn index                             -}
{- • A global variable, imported from a module. As modules can be nested, we   -}
{-   represent the path through a vector of text. These are called Qualified   -}
{-   Names.                                                                    -}


type QualName = Vector Text
data Name = QName QualName | DeBruijn Int Text

instance Eq Name where  
  (==) (QName      t1) (QName t2)      = t1 == t2
  (==) (DeBruijn n1 _) (DeBruijn n2 _) = n1 == n2
  (==) _ _                             = False

instance Show Name where  
  show (QName vec) = show vec
  show (DeBruijn n v) = unpack v <> "[" <> show n <> "]"

instance Pretty Name where  
  pretty (QName vec) = dots vec where 
    dots ::  QualName -> Doc ann 
    dots vec = case length vec of 
      0 -> "<empty name>"
      1 -> pretty $ head vec
      _ -> foldl (\s v -> s <> "." <> pretty v) (pretty $ head vec) vec  
  pretty (DeBruijn _ v) = pretty v

