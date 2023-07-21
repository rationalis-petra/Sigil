module Interactive
  ( InteractiveOpts(..)
  , interactive ) where


import Prelude hiding (getLine, putStr)

import Control.Monad.Except (MonadError, throwError, catchError)
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
import Glyph.Interpret.Interpreter
import Glyph.Concrete.Internal


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

interactive :: forall m e s t. (MonadError GlyphDoc m, MonadGen m, Environment Name e)
  => Interpreter m (e (Maybe InternalCore, InternalCore)) s t -> InteractiveOpts -> IO ()
interactive (Interpreter {..}) = loop start_state
  where
    loop :: s -> InteractiveOpts -> IO ()
    loop state opts =  do
      putStr "> "
      hFlush stdout
      line <- getLine
      if (should_quit line) then do
        (result, state') <- run state $ eval_line line 
        case result of
          Right (val, ty) -> do
            putDocLn $ "final value:" <+> nest 2 (pretty val)
            putDocLn $ "type" <+> nest 2 (pretty ty)
          Left err -> putDocLn err
        loop state' opts
      else
        (run state stop) >> pure ()
    
    should_quit :: Text -> Bool
    should_quit ":q" = True
    should_quit _ = False

    eval_line :: Text -> m (InternalCore, InternalCore)
    eval_line line = do
      env <- get_env Nothing 
      parsed <- parseToErr (core default_precs <* eof) "console-in" line 
      resolved <- resolve_closed parsed
        `catchError` (throwError . (<+>) "Resolution:")
      (term, ty) <- infer interp_eval env resolved
        `catchError` (throwError . (<+>) "Inference:")
      norm <- interp_eval env ty term
        `catchError` (throwError . (<+>) "Normalization:")
      pure (norm, ty)

    interp_eval :: e (Maybe InternalCore, InternalCore) -> InternalCore -> InternalCore -> m InternalCore
    interp_eval env ty val = do
      ty' <- reify ty
      val' <- reify val
      result <- eval env ty' val'
      reflect result 
