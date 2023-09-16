{-# LANGUAGE ApplicativeDo #-}
module Main (main) where

import Prelude hiding (putStrLn)

import Control.Monad.Except (MonadError)
import Data.Text.IO
import Data.Text (pack)

import Options.Applicative
import Prettyprinter.Render.Sigil

import Sigil.Abstract.Environment (Environment, Env, Name, MonadGen)
import Sigil.Interpret.Interpreter 
import Sigil.Interpret.Canonical 
import Sigil.Concrete.Internal
import Interactive
import Server

data Backend = Native | JVM | Javascript | WASM
  deriving (Show, Read, Eq)

interactive_opts :: Parser (InteractiveOpts, Backend)
interactive_opts = do
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
  pure (InteractiveOpts file, backend)

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
  | InteractiveCommand (InteractiveOpts, Backend)
  | ServerCommand (ServerOpts, Backend)
  deriving (Show, Read, Eq)

sigil_opts :: Parser Command
sigil_opts = subparser $ 
  command "compile" (info (CompileCommand <$> compile_opts) (progDesc "Compile a Sigil program"))
  <>
  command "server" (info (ServerCommand <$> server_opts) (progDesc "Launch the Sigil language server"))
  <>
  command "interactive" (info (InteractiveCommand <$> interactive_opts) (progDesc "Launch Sigil in interactive mode"))

main :: IO ()
main = do
  command <- execParser $ info (sigil_opts <**> helper)
    ( fullDesc 
    <> progDesc "Compile, Run or Develop a Sigil Program"
    <> header "An implementation of the Sigil Language" )
  case command of 
    InteractiveCommand (c, backend) -> run_with_backend backend interactive c
    ServerCommand (s, backend) -> run_with_backend backend server s
    _ -> putStrLn $ pack $ show command


run_with_backend ::
  Backend
  -> (forall m e s t. (MonadError SigilDoc m, MonadGen m, Environment Name e) =>
      Interpreter m SigilDoc (e (Maybe InternalCore, InternalCore)) s t -> a -> IO ())
  -> a -> IO ()
run_with_backend backend func val = case backend of
  Native -> func (canonical_interpreter spretty
                  :: Interpreter (CanonM SigilDoc) SigilDoc (Env (Maybe InternalCore, InternalCore)) (World InternalModule) InternalCore) val
  b -> putStrLn $ pack ("Cannot run with backend:" <> show b)
