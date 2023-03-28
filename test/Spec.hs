import Prelude hiding (putStrLn)

import Control.Monad (join)
import Data.Text.IO (putStrLn)

import Prettyprinter
import Prettyprinter.Render.Glyph

import TestFramework
import Spec.Glyph.Abstract.Syntax
import Spec.Glyph.Abstract.NameResolution
import Spec.Glyph.Abstract.Term
import Spec.Glyph.Parse


main :: IO ()
main = runall
  [ parse_spec
  , resolve_spec
  , syntax_spec
  , term_spec
  ]


runall :: [TestGroup] -> IO ()
runall group = do
  errors <- join <$> mapM (rungroup 0) group
  if (not $ null errors) then do
    putStrLn "\nErrors:"
    mapM_ putDoc $ map (indent 2) errors
  else 
    pure ()

rungroup :: Int -> TestGroup-> IO [Doc GlyphStyle]
rungroup nesting (TestGroup name children) = do
  putDocLn $ indent (nesting * 2) $ pretty name
  case children of
    Left subgruops -> join <$> mapM (rungroup (nesting + 1)) subgruops
    
    Right tests -> runtests (nesting + 1) tests

runtests :: Int -> [Test] -> IO [Doc GlyphStyle]
runtests nesting tests = join <$> mapM runtest tests where
  runtest (Test name Nothing) = do
    putDocLn $ annotate (fg_colour green) $ indent (nesting * 2) $ pretty name
    pure []
  runtest (Test name (Just err)) = do
    putDocLn $ annotate (fg_colour red) $ indent (nesting * 2) $ pretty name
    pure [annotate (fg_colour red) (pretty name) <+> annotate (fg_colour yellow) err]
