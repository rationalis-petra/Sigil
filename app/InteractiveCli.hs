module InteractiveCli
  ( InteractiveCliOpts(..)
  , interactive_cli ) where


import Prelude hiding (mod, getLine, putStr, putStrLn, readFile, null)

import Control.Monad (void)
import Control.Monad.Except (MonadError)
import Control.Lens (makeLenses, (^.), (%~), _1, _2)
import Data.List.NonEmpty
import Data.Text (Text, unpack, null)
import Data.Text.IO
import System.IO hiding (getLine, putStr, putStrLn, readFile)

import qualified Text.Megaparsec as Megaparsec
import Text.Megaparsec hiding (parse, runParser)
import Text.Megaparsec.Char as C
import Prettyprinter
import Prettyprinter.Render.Sigil

import Sigil.Abstract.Names
import Sigil.Abstract.Syntax
import Sigil.Abstract.Environment
import Sigil.Parse.Lexer
import Sigil.Interpret.Interpreter
import Sigil.Concrete.Internal

import InterpretUtils

newtype InteractiveCliOpts = InteractiveCliOpts
  { ifile :: Text
  }
  deriving (Show, Read, Eq)


newtype InteractiveState = InteractiveState
  { _location :: (Text, [ImportDef])
  }
  deriving (Show, Eq)

$(makeLenses ''InteractiveState)

data Command
  = Eval Text
  | Import ImportDef
  | Load Text
  | Quit
  | Malformed SigilDoc

interactive_cli :: forall m e s t. (MonadError SigilDoc m, MonadGen m, Environment Name e)
  => Interpreter m SigilDoc (e (Maybe InternalCore, InternalCore)) s t -> InteractiveCliOpts -> IO ()
interactive_cli interp@(Interpreter {..}) opts = do
    s <- if not (null (ifile opts)) then eval_file "sigil-user" (ifile opts) start_state else pure start_state
    loop s (InteractiveState ("sigil-user", []))
  where
    loop :: s -> InteractiveState -> IO ()
    loop state istate =  do
      putStr "> "
      hFlush stdout
      line <- getLine
      case read_command line of  
        Eval line -> do
          (result, state') <-
            run state $ eval_expr interp (istate^.location._1) (istate^.location._2) line 
          case result of
            Right (val, ty) -> do
              putDocLn $ "val:" <+> nest 2 (pretty val)
              putDocLn $ "type:" <+> nest 2 (pretty ty)
            Left err -> putDocLn $ err
          loop state' istate

        Load filename -> do 
          state' <- eval_file (istate^.location._1) filename state
          loop state' istate
          
        Import def -> loop state ((location._2 %~ (def :)) istate)

        Quit -> void $ run state stop

        Malformed err -> do
          putDocLn $ "Malformed command: " <+> err
          loop state istate

    eval_file :: Text ->Text -> s -> IO s
    eval_file package_name filename state = do
      text <- readFile (unpack filename)
      (result, state') <- run state $ do
        mod <- eval_mod interp package_name filename text
        intern_module package_name (mod^.module_header) mod
        pure mod
        
      case result of
        Left err -> putDocLn err
        _ -> pure ()
      pure state'

read_command :: Text -> Command
read_command cmd = case Megaparsec.runParser command_parser "console-in" cmd of
  Right cmd -> cmd
  Left err -> Malformed $ pretty $ errorBundlePretty err

type CmdParser = Parsec Text Text

command_parser :: CmdParser Command
command_parser = do
  c <- sc *> lookAhead (satisfy (const True))
  case c of  
    ';' -> do
      void $ C.char ';'
      cmd <- ( (const Quit <$> symbol "q")
        <|> (symbol "import" *> pImport)
        <|> (symbol "load" *> pLoadFile))
      sc <* eof
      pure cmd
    _ -> Eval <$> takeWhileP (Just "any") (const True)
  where 
    pImport = do
      let
        sep :: CmdParser a -> CmdParser b -> CmdParser [a]
        sep p separator = ((: []) <$> p <|> pure []) >>= \v ->
            (v <> ) <$> many (try (separator *> p))

      l <- sep anyvar (C.char '.' <* sc)
      path <- case l of 
        [] -> fail "import path must be nonempty"
        (x:xs) -> pure (Path $ x:|xs)
      modifier <- pModifier <|> pure ImSingleton
      pure . Import $ Im (path, modifier)

    pModifier :: CmdParser ImportModifier
    pModifier = 
      const ImWildcard <$> (lexeme (C.char '.') *> symbol "(..)")

    pLoadFile = do  
      Load <$>
        takeWhileP (Just "non-whitespace")
          (\case
            ' '  -> False
            '\t' -> False
            '\n' -> False
            '\r' -> False
            _    -> True)
