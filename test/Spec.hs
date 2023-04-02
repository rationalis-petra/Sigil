import Prelude hiding (putStrLn)

import Control.Monad (when, join)
import Data.Text.IO (putStrLn)

import Prettyprinter
import Prettyprinter.Render.Glyph
import Options.Applicative

import TestFramework
import Spec.Glyph.Abstract.Syntax
import Spec.Glyph.Abstract.NameResolution
import Spec.Glyph.Abstract.Term
import Spec.Glyph.Abstract.Substitution
import Spec.Glyph.Abstract.Unify
import Spec.Glyph.Parse

data Verbosity = Errors | Groups | Verbose
  deriving (Read, Show, Eq, Ord)

data Config = Config
  { verbosity :: Verbosity }

main :: IO ()
main = runall tests =<< execParser opts
  where 
    opts = info (config <**> helper)
      ( fullDesc
      <> progDesc "Run all tests for Glyph"
      <> header "Glyph test suite" )

config :: Parser Config  
config = Config
  <$> option auto
    (  long "verbosity"
    <> short 'v'
    <> help "Verbosity: can be verbose, groups or errors"
    <> value Groups)

tests :: [TestGroup]
tests = 
  [ parse_spec
  , resolve_spec
  , syntax_spec
  , term_spec
  , subst_spec
  , unify_spec
  ]

runall :: [TestGroup] -> Config -> IO ()
runall group config = do
  errors <- join <$> mapM (rungroup 0) group
  when (not $ null errors) $ do
    putStrLn "\nErrors:"
    mapM_ putDocLn $ map (indent 2) errors
  where
    rungroup :: Int -> TestGroup-> IO [Doc GlyphStyle]
    rungroup nesting (TestGroup name children) = do
      when (verbosity config >= Groups) $
        putDocLn $ indent (nesting * 2) $ pretty name
      case children of
        Left subgruops -> join <$> mapM (rungroup (nesting + 1)) subgruops
        
        Right tests -> runtests (nesting + 1) tests
    
    runtests :: Int -> [Test] -> IO [Doc GlyphStyle]
    runtests nesting tests = join <$> mapM runtest tests where
      runtest (Test name Nothing) = do
        when (verbosity config >= Verbose) $
          putDocLn $ annotate (fg_colour green) $ indent (nesting * 2) $ pretty name
        pure []
      runtest (Test name (Just err)) = do
        when (verbosity config >= Verbose) $
          putDocLn $ annotate (fg_colour red) $ indent (nesting * 2) $ pretty name
        pure [annotate (fg_colour red) (pretty name) <+> annotate (fg_colour yellow) err]
  
