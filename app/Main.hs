{-# LANGUAGE ApplicativeDo #-}
module Main (main) where

import Prelude hiding (putStrLn)

import Control.Monad.Except (MonadError)
import Data.Text.IO
import Data.Text (pack)

import Options.Applicative
import Prettyprinter.Render.Sigil

import Sigil.Abstract.Names (MonadGen)
import Sigil.Interpret.Interpreter 
import Sigil.Interpret.Canonical.Environment
import Sigil.Interpret.Canonical.World
import Sigil.Interpret.Canonical 
import InteractiveTui
import InteractiveCli
import Server

data Backend = Native | JVM | Javascript | WASM
  deriving (Show, Read, Eq)

interactive_cli_opts :: Parser (InteractiveCliOpts, Backend)
interactive_cli_opts = do
  file <- strOption
    ( long "file"
    <> short 'f'
    <> value ""
    <> help "Specify what file to run (if any)" )
  backend <- option auto
    ( long "backend"
    <> short 'b'
    <> showDefault
    <> value Native )
  pure (InteractiveCliOpts file, backend)

interactive_tui_opts :: Parser (InteractiveTuiOpts, Backend)
interactive_tui_opts = do
  backend <- option auto
    ( long "backend"
    <> short 'b'
    <> showDefault
    <> value Native )
  pure (InteractiveTuiOpts, backend)

data CompileOpts = CompileOpts
  { cfile :: String
  , backend :: Backend
  }
  deriving (Show, Read, Eq)

compile_opts :: Parser CompileOpts
compile_opts = CompileOpts
  <$> strOption
    ( long "input-file"
    <> short 'i'
    <> help "Specify an (input) file to compile" )
  <*> option auto 
    ( long "backend"
    <> short 'b'
    <> value Native )


server_opts :: Parser (ServerOpts, Backend)
server_opts = do
  port <- option auto
    ( long "port"
    <> help "What port the server runs from"
    <> showDefault
    <> value 8801
    <> metavar "INT" )
  backend <- option auto
    ( long "backend"
    <> short 'b'
    <> showDefault
    <> value Native )
  pure (ServerOpts port, backend)

data Command
  = CompileCommand CompileOpts
  | InteractiveCliCommand (InteractiveCliOpts, Backend)
  | InteractiveTuiCommand (InteractiveTuiOpts, Backend)
  | ServerCommand (ServerOpts, Backend)
  deriving (Show, Read, Eq)

sigil_opts :: Parser Command
sigil_opts = subparser $ 
  command "compile" (info (CompileCommand <$> compile_opts) (progDesc "Compile a Sigil program"))
  <>
  command "server" (info (ServerCommand <$> server_opts) (progDesc "Launch the Sigil language server"))
  <>
  command "interactive-line" (info (InteractiveCliCommand <$> interactive_cli_opts) (progDesc "Launch Sigil in interactive mode (command line interface)"))
  <>
  command "interactive" (info (InteractiveTuiCommand <$> interactive_tui_opts) (progDesc "Launch Sigil in interactive mode (terminal ui interface)"))

main :: IO ()
main = do
  command <- execParser $ info (sigil_opts <**> helper)
    ( fullDesc 
    <> progDesc "Compile, Run or Develop a Sigil Program"
    <> header "An implementation of the Sigil Language" )
  case command of 
    InteractiveCliCommand (c, backend) -> run_with_backend backend interactive_cli c
    InteractiveTuiCommand (c, backend) -> run_with_backend backend interactive_tui c
    ServerCommand (s, backend) -> run_with_backend backend server s
    _ -> putStrLn $ pack $ show command


run_with_backend ::
  Backend
  -> (forall m env s. (MonadError SigilDoc m, MonadGen m) =>
      Interpreter m SigilDoc env s -> a -> IO ())
  -> a -> IO ()
run_with_backend backend func val = case backend of
  Native -> func (canonical_interpreter spretty
                 :: Interpreter (CanonM SigilDoc) SigilDoc (CanonEnv (CanonM SigilDoc)) (World (CanonM SigilDoc))) val
                 -- :: Interpreter (CanonM SigilDoc) SigilDoc (Env (Maybe InternalCore, InternalCore)) Context InternalCore (Formula Name InternalCore)) val
  b -> putStrLn $ pack ("Cannot run with backend:" <> show b)
