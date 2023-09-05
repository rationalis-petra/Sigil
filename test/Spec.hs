import Prelude hiding (putStrLn)

import Control.Monad (when, join, unless)
import Data.Text.IO (putStrLn)

import Prettyprinter
import Prettyprinter.Render.Sigil
import Options.Applicative

import TestFramework

import Spec.Sigil.Abstract
import Spec.Sigil.Parse
import Spec.Sigil.Interpret
import Spec.Sigil.Analysis


data Verbosity = Errors | Groups | Verbose
  deriving (Read, Show, Eq, Ord)

newtype Config = Config
  { verbosity :: Verbosity }

main :: IO ()
main = runall tests =<< execParser opts
  where 
    opts = info (config <**> helper)
      ( fullDesc
      <> progDesc "Run all tests for Sigil."
      <> header "Sigil. test suite" )

config :: Parser Config  
config = Config
  <$> option auto
    (  long "verbosity"
    <> short 'v'
    <> help "Verbosity: can be verbose, groups or errors"
    <> value Groups)

tests :: [TestGroup]
tests = 
  [ abstract_spec
  , parse_spec
  , interpret_spec
  , analysis_spec
  ]

runall :: [TestGroup] -> Config -> IO ()
runall group config = do
  errors <- join <$> mapM (rungroup 0) group
  unless (null errors) $ do
    putStrLn "\nErrors:"
    mapM_ (putDocLn . indent 2) errors
  where
    rungroup :: Int -> TestGroup-> IO [Doc SigilStyle]
    rungroup nesting (TestGroup name children)  = do
      when (verbosity config >= Groups)
        (putDocLn $ indent (nesting * 2) $ pretty name)
      case children of  
          Left subgruops -> map ((annotate (fg_colour red) $ pretty name <> ".") <>) . join <$> mapM (rungroup (nesting + 1)) subgruops
          Right tests ->
            map ((annotate (fg_colour red) $ pretty name <> ".") <>) <$> runtests (nesting + 1) tests
    
    runtests :: Int -> [Test] -> IO [Doc SigilStyle]
    runtests nesting tests = join <$> mapM runtest tests where
      runtest (Test name Nothing) = do
        when (verbosity config >= Verbose) $
          putDocLn $ annotate (fg_colour green) $ indent (nesting * 2) $ pretty name
        pure []
      runtest (Test name (Just err)) = do
        when (verbosity config >= Verbose) $
          putDocLn $ annotate (fg_colour red) $ indent (nesting * 2) $ pretty name
        pure [annotate (fg_colour red) (pretty name) <+> annotate (fg_colour yellow) err]
  
