module Interactive
  ( InteractiveOpts(..)
  , interactive ) where


import Prelude hiding (mod, getLine, putStr, putStrLn, readFile)

import Control.Monad (void)
import Control.Monad.Except (MonadError, throwError, catchError)
import Control.Lens (makeLenses, (^.), (%~))
import Data.List.NonEmpty
import Data.Text (Text, unpack)
import Data.Text.IO
import System.IO hiding (getLine, putStr, putStrLn, readFile)

import Text.Megaparsec hiding (parse, runParser)
import Text.Megaparsec.Char as C
import Prettyprinter
import Prettyprinter.Render.Sigil

import Sigil.Abstract.Names
import Sigil.Abstract.Syntax
import Sigil.Abstract.Environment
import Sigil.Parse.Lexer
import Sigil.Parse
import Sigil.Analysis.NameResolution
import Sigil.Analysis.Typecheck
import Sigil.Interpret.Interpreter
import Sigil.Concrete.Internal


newtype InteractiveOpts = InteractiveOpts
  { ifile :: Text
  }
  deriving (Show, Read, Eq)


newtype InteractiveState = InteractiveState
  { _imports :: [ImportDef]
  }
  deriving (Show, Eq)

$(makeLenses ''InteractiveState)

data Command
  = Eval Text
  | Import ImportDef
  | Quit
  | Malformed SigilDoc

interactive :: forall m e s t. (MonadError SigilDoc m, MonadGen m, Environment Name e)
  => Interpreter m SigilDoc (e (Maybe InternalCore, InternalCore)) s t -> InteractiveOpts -> IO ()
interactive (Interpreter {..}) opts = do
    s <- eval_file (ifile opts) start_state
    loop s (InteractiveState [])
  where
    loop :: s -> InteractiveState -> IO ()
    loop state istate =  do
      putStr "> "
      hFlush stdout
      line <- getLine
      case read_command line of  
        Eval line -> do
          (result, state') <- run state $ eval_line istate line 
          case result of
            Right (val, ty) -> do
              putDocLn $ "val:" <+> nest 2 (pretty val)
              putDocLn $ "type:" <+> nest 2 (pretty ty)
            Left err -> putDocLn $ err
          loop state' istate

        Import def -> loop state ((imports %~ (def :)) istate)

        Quit -> void $ run state stop

        Malformed err -> do
          putDocLn $ "Malformed command: " <+> err
          loop state istate
       

    eval_line :: InteractiveState -> Text -> m (InternalCore, InternalCore)
    eval_line istate line = do
      env <- get_env ("repl" :| []) (istate^.imports)
      precs <- get_precs ("repl" :| []) (istate^.imports)
      resolution <- get_resolve ("repl" :| []) (istate^.imports)
      parsed <- parseToErr (core precs <* eof) "console-in" line 
      resolved <- resolve_closed resolution parsed
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
        intern_module (mod^.module_header) mod
        pure mod
        
      case result of
        Left err -> putDocLn err
        _ -> pure ()
      pure state'

    check_mod :: Text -> Text -> m InternalModule
    check_mod filename file = do
      parsed <- parse (mod get_precs <* eof) filename file 
        `catchError` (throwError . (<+>) "Parse:")

      resolve_vars <- get_resolve (parsed^.module_header) (parsed^.module_imports)
      resolved <- resolve_module (parsed^.module_header) (fmap Right resolve_vars) parsed
        `catchError` (throwError . (<+>) "Resolution:")

      env <- get_env (parsed^.module_header) (parsed^.module_imports)
      check_module (CheckInterp interp_eval interp_eq spretty) env resolved
        `catchError` (throwError . (<+>) "Inference:")

read_command :: Text -> Command
read_command cmd = case parseToErr command_parser "console-in" cmd of
  Right cmd -> cmd
  Left err -> Malformed err

type Parser = Parsec Text Text

command_parser :: Parser Command
command_parser = do
  c <- sc *> lookAhead (satisfy (const True))
  case c of  
    ';' -> do
      void $ C.char ';'
      cmd <- ( (const Quit <$> symbol "q")
        <|> (symbol "import" *> pImport))
      sc <* eof
      pure cmd
    _ -> Eval <$> takeWhileP (Just "any") (const True)
  where 
    pImport = do
      let
        sep :: Parser a -> Parser b -> Parser [a]
        sep p separator = ((: []) <$> p <|> pure []) >>= \v ->
            (v <> ) <$> many (try (separator *> p))

      l <- sep anyvar (C.char '.' <* sc)
      path <- case l of 
        [] -> fail "import path must be nonempty"
        (x:xs) -> pure (x:|xs)
      modifier <- pModifier <|> pure ImSingleton
      pure $ Import (path, modifier)

    pModifier :: Parser ImportModifier
    pModifier = 
      const ImWildcard <$> (lexeme (C.char '.') *> symbol "(..)")
