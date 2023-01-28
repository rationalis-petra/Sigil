module Spec.Glyph.NameResolution (resolve_spec) where

import Prelude hiding (putStrLn)
import Control.Monad (when)
import Data.Vector (singleton)
import Data.Text (Text)
import Data.Text.IO

import Prettyprinter
import Prettyprinter.Render.Text

import Glyph.Name
import Glyph.Core
import Glyph.NameResolution

import Spec.Glyph.CoreUD


resolve_spec :: IO ()
resolve_spec = do_tests tests >> putStrLn "resolution suit passed"

do_tests :: [(Core Text UD, Core Name UD)] -> IO ()
do_tests = mapM_ do_test where
  do_test (val, result) = 
    when (resolve val /= result) (print_bad val result)

  print_bad l r = putDoc doc >> (putStrLn "") where
    doc = pretty l <+> "is does not resolve to " <+> pretty r

tests :: [(Core Text UD, Core Name UD)]
tests =
  [ (var "x", qvar "x")
  , (abs "y" (var "y"), abs "y" (dbv 0 "y"))
  , (abs "y" (var "x"), abs "y" (qvar "x"))
  ]
  where
    var = Var void
    abs = Abs void
    dbv n t = Var void $ DeBruijn n t
    qvar v = Var void $ QName $ singleton v
  

