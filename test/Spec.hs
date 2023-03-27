import Prelude hiding (putStrLn, replicate)

import Data.Text (Text, replicate)
import Data.Text.IO (putStrLn)

import Prettyprinter
import Prettyprinter.Render.Text

import TestFramework
import Spec.Glyph.Abstract.Syntax
import Spec.Glyph.Abstract.NameResolution
import Spec.Glyph.Parse


main :: IO ()
main = runall
  [ parse_spec
  , resolve_spec
  , syntax_spec
  ]


runall :: [TestGroup ann] -> IO () 
runall = mapM_ (rungroup 0) 

rungroup :: Int -> TestGroup ann -> IO ()
rungroup nesting (TestGroup name children) = do
  putNested nesting name
  case children of
    Left subgruops -> mapM_ (rungroup (nesting + 1)) subgruops
    
    Right tests -> runtests (nesting + 1) tests

runtests :: Int -> [Test ann] -> IO ()
runtests nesting = mapM_ runtest where
  runtest (Test name Nothing) = do
    putNested nesting name
  runtest (Test name (Just err)) = do
    putNested nesting $ name <> " failed: "
      <> (renderStrict $ layoutPretty defaultLayoutOptions err)

putNested :: Int -> Text -> IO () 
putNested n text = putStrLn (replicate (n * 2) " " <> text)
