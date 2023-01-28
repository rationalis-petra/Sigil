module Glyph.NameResolution (resolve) where

import Prelude hiding (lookup)
import Data.Map (Map, lookup, insert, empty)
import Data.Vector (singleton)
import Data.Text (Text)

import Glyph.Name
import Glyph.Core


resolve :: Core Text χ -> Core Name χ 
resolve core = resolve' empty core where

resolve' :: Map Text Int -> Core Text χ -> Core Name χ 
resolve' vars term = case term of 
  Coreχ χ -> Coreχ χ
  Uni χ n -> Uni χ n
  Var χ text -> Var χ $ case lookup text vars of  
    Just val -> DeBruijn val text 
    Nothing -> QName $ singleton $ text
  Prd χ var a b -> Prd χ var (resolve' vars a) (resolve' (add var vars) b)
  Abs χ var e -> Abs χ var (resolve' (add var vars) e)
  App χ l r -> App χ (resolve' vars l) (resolve' vars r)

add :: Text -> Map Text Int -> Map Text Int 
add v = insert v 0 . fmap (+ 1)  
