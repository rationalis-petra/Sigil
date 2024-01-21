module InteractiveCli
  ( InteractiveCliOpts(..)
  , interactive_cli ) where


import Prelude hiding (mod, getLine, putStr, putStrLn, readFile, null)
import System.IO hiding (getLine, putStr, putStrLn, readFile)

import Control.Monad (void)
import Control.Monad.Except (MonadError)
import Control.Lens (makeLenses, (^.), (%~), _1, _2)
import Data.List.NonEmpty
import Data.Text (Text, unpack, null)
import qualified Data.Map as Map
import Data.Text.IO

import qualified Text.Megaparsec as Megaparsec
import Text.Megaparsec hiding (parse, runParser)
import Text.Megaparsec.Char as C
import Prettyprinter
import Prettyprinter.Render.Sigil

import Sigil.Abstract.Names
import Sigil.Abstract.Syntax
import Sigil.Parse.Lexer
import Sigil.Interpret.Interpreter

import InterpretUtils
import Actions.Package

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
  | LoadPackage Text
  | Quit
  | Malformed SigilDoc

interactive_cli :: forall m env s. (MonadError SigilDoc m, MonadGen m)
  => Interpreter m SigilDoc env s -> InteractiveCliOpts -> IO ()
interactive_cli interp@(Interpreter {..}) opts = do
    (merr, state') <- run start_state $ do
      intern_package
        "sigil-user" (Package
                      (PackageHeader "sigil-user" [] [])
                      (MTree Map.empty))
      pure $ ()
    case merr of
      Right () -> pure ()
      Left err -> putDocLn ("error in initialization:" <+> err)

    s <- if not (null (ifile opts)) then eval_file "sigil-user" (ifile opts) state' else pure state'
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

        LoadPackage filename -> do 
          out <- build_dependency_list [unpack filename] 
          case out of  
            Right _ -> loop state istate
            Left err -> do
              putDocLn err 
              loop state istate
          
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
        intern_module (mod^.module_header) mod
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
        <|> try (symbol "load" *> (Load <$> pLoadFile))
        <|> (symbol "load-package" *> (LoadPackage <$> pLoadFile)))
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
        (x:xs) -> pure (x:|xs)
      modifier <- pModifier <|> pure ImSingleton
      pure . Import $ Im (path, modifier)

    pModifier :: CmdParser ImportModifier
    pModifier = 
      const ImWildcard <$> (lexeme (C.char '.') *> symbol "(..)")

    pLoadFile =
      takeWhile1P (Just "non-whitespace")
      (\case
          ' '  -> False
          '\t' -> False
          '\n' -> False
          '\r' -> False
          _    -> True)
