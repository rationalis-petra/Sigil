module Interactive
  ( InteractiveOpts(..)
  , interactive ) where


import Prelude hiding (getLine, putStr)

import Control.Monad (unless)
import Control.Monad.Except (ExceptT, runExceptT)
import qualified Data.Map as Map
import Data.Text
import Data.Text.IO
import System.IO hiding (getLine, putStr)

import Text.Megaparsec hiding (runParser)
import Prettyprinter
import Prettyprinter.Render.Glyph

import Glyph.Abstract.Environment
import Glyph.Parse  
import Glyph.Parse.Mixfix
import Glyph.Analysis.NameResolution
import Glyph.Analysis.Typecheck
import Glyph.Interpret.Term
import Glyph.Concrete.Typed


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
          Right (val, ty) -> do
            putDocLn $ "final value:" <+> nest 2 (pretty val)
            putDocLn $ "type" <+> nest 2 (pretty ty)
          Left err -> putDocLn err
        loop () opts
    
    should_quit :: Text -> Bool
    should_quit ":q" = True
    should_quit _ = False
    
    eval_line :: Text -> Either GlyphDoc (TypedCore, TypedCore)
    eval_line line = run_gen $ runExceptT $ meval line

    meval :: Text -> ExceptT GlyphDoc Gen (TypedCore, TypedCore)
    meval line = do
      parsed <- parseToErr (core (Precedences Map.empty "infixl" "prefix" "postfix" "closed") <* eof) "console-in" line 
      resolved <- resolve parsed
      (term, ty) <- infer (Map.empty :: Map.Map Integer (TypedCore, TypedCore)) resolved
      norm <- normalize (Map.empty :: Map.Map Integer TypedCore) ty term
      pure $ (norm, ty) 
