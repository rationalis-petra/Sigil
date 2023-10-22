module Interactive
  ( InteractiveOpts(..)
  , interactive ) where


import Prelude hiding (mod, getLine, putStr, readFile)

import Control.Monad (void)
import Control.Monad.Except (MonadError, throwError, catchError)
import Data.List.NonEmpty
import Data.Text (Text, unpack)
import Data.Text.IO
import System.IO hiding (getLine, putStr, readFile)

import Text.Megaparsec hiding (parse, runParser)
import Prettyprinter
import Prettyprinter.Render.Sigil

import Sigil.Abstract.Environment
import Sigil.Parse  
import Sigil.Analysis.NameResolution
import Sigil.Analysis.Typecheck
import Sigil.Interpret.Interpreter
import Sigil.Concrete.Internal


newtype InteractiveOpts = InteractiveOpts
  { ifile :: Text
  }
  deriving (Show, Read, Eq)


interactive :: forall m e s t. (MonadError SigilDoc m, MonadGen m, Environment Name e)
  => Interpreter m SigilDoc (e (Maybe InternalCore, InternalCore)) s t -> InteractiveOpts -> IO ()
interactive (Interpreter {..}) opts = do
    s <- eval_file (ifile opts) start_state
    loop s opts 
  where
    loop :: s -> InteractiveOpts -> IO ()
    loop state opts =  do
      putStr "> "
      hFlush stdout
      line <- getLine
      if not (should_quit line) then do
        (result, state') <- run state $ eval_line line 
        case result of
          Right (val, ty) -> do
            putDocLn $ "val:" <+> nest 2 (pretty val)
            putDocLn $ "type:" <+> nest 2 (pretty ty)
          Left err -> putDocLn $ err
        loop state' opts
      else
        void $ run state stop
   
    should_quit :: Text -> Bool
    should_quit ";q" = True
    should_quit _ = False

    eval_line :: Text -> m (InternalCore, InternalCore)
    eval_line line = do
      env <- get_env ("repl" :| []) []
      precs <- get_precs ("repl" :| []) []
      parsed <- parseToErr (core precs <* eof) "console-in" line 
      resolved <- resolve_closed parsed
        `catchError` (throwError . (<+>) "Resolution:")
      (term, ty) <- infer (CheckInterp interp_eval interp_eq spretty) env resolved
        `catchError` (throwError . (<+>) "Inference:")
      norm <- interp_eval id env ty term
        `catchError` (throwError . (<+>) "Normalization:")
      pure (norm, ty)

    interp_eval :: (SigilDoc -> SigilDoc) -> e (Maybe InternalCore, InternalCore) -> InternalCore -> InternalCore -> m InternalCore
    interp_eval f env ty val = do
      ty' <- reify ty
      val' <- reify val
      result <- eval f env ty' val'
      reflect result 

    interp_eq :: (SigilDoc -> SigilDoc) -> e (Maybe InternalCore, InternalCore) -> InternalCore -> InternalCore -> InternalCore -> m Bool
    interp_eq f env ty l r = do
      ty' <- reify ty
      l' <- reify l
      r' <- reify r
      norm_eq f env ty' l' r'

    eval_file :: Text -> s -> IO s
    eval_file filename state = do
      text <- readFile (unpack filename)
      (result, state') <- run state $ do
        mod <- check_mod filename text
        intern_module ("repl" :| []) mod
        pure mod
        
      case result of
        Right modul -> do
          putStr "\n"
          putDocLn $ "module:" <+> nest 2 (pretty modul)
          putStr "\n"
        Left err -> putDocLn err
      pure state'

    check_mod :: Text -> Text -> m InternalModule
    check_mod filename file = do
      env <- get_env (filename :| []) []
      precs <- get_precs (filename :| []) []
      parsed <- parse (mod (\_ _ -> pure precs) <* eof) filename file 
        `catchError` (throwError . (<+>) "Parse:")
      resolved <- resolve_closed parsed
        `catchError` (throwError . (<+>) "Resolution:")
      check_module (CheckInterp interp_eval interp_eq spretty) env resolved
        `catchError` (throwError . (<+>) "Inference:")
