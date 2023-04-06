module Interactive
  ( InteractiveOpts(..)
  , interactive ) where


import Prelude hiding (getLine, putStr)

import Control.Monad (unless)
import qualified Data.Set as Set
import qualified Data.Map as Map
import Data.Text
import Data.Text.IO

import System.IO hiding (getLine, putStr)
import Prettyprinter
import Prettyprinter.Render.Glyph

import Glyph.Concrete.Parsed
import Glyph.Parse  


data InteractiveOpts = InteractiveOpts
  { ifile :: String
  }
  deriving (Show, Read, Eq)


interactive :: InteractiveOpts -> IO ()
interactive = loop default_env
  where
    default_env :: ()
    default_env = ()

    loop :: () -> InteractiveOpts -> IO ()
    loop _ opts = do
      putStr "> "
      hFlush stdout
      line <- getLine
      unless (should_quit line) $ do
        case eval_line line of
          Right val -> putDocLn $ pretty val
          Left err -> putDocLn err
        loop () opts
    
    should_quit :: Text -> Bool
    should_quit ":q" = True
    should_quit _ = False
    
    eval_line :: Text -> Either GlyphDoc RawCore
    eval_line line = case runParser (core (Precedences Map.empty Set.empty)) "console-in" line of 
      Right val -> Right val
      Left err -> Left $ pretty err
