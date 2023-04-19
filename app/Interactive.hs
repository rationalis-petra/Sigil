module Interactive
  ( InteractiveOpts(..)
  , interactive ) where


import Prelude hiding (getLine, putStr)

import Control.Monad (unless)
import Control.Monad.Except (ExceptT, runExceptT, throwError, catchError)
import qualified Data.Map as Map
import qualified Data.Set as Set
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

default_precs :: Precedences
default_precs = Precedences
  (Map.fromList
   [ ("sum", PrecedenceNode Set.empty (Set.fromList ["prod"]))
   , ("prod", PrecedenceNode Set.empty (Set.fromList ["ppd"]))
   , ("ppd", PrecedenceNode Set.empty (Set.fromList ["tight"]))
   , ("ctrl", PrecedenceNode Set.empty (Set.fromList ["tight"]))
   , ("tight", PrecedenceNode Set.empty (Set.fromList ["tight"]))
   , ("tight", PrecedenceNode Set.empty (Set.fromList ["close"]))
   , ("close", PrecedenceNode Set.empty Set.empty)
   ])
  "sum" "ppd" "ppd" "close"

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
      parsed <- parseToErr (core default_precs <* eof) "console-in" line 
      resolved <- resolve parsed
        `catchError` (throwError . (<+>) "resolution:")
      (term, ty) <- infer (env_empty :: Env (Maybe TypedCore, TypedCore)) resolved
        `catchError` (throwError . (<+>) "inference:")
      norm <- normalize (env_empty :: Env (Maybe TypedCore, TypedCore)) ty term
        `catchError` (throwError . (<+>) "normalization:")
      pure $ (norm, ty) 
