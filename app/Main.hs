{-# LANGUAGE ApplicativeDo #-}
module Main (main) where

import Prelude hiding (putStrLn)

import Control.Monad.Except (MonadError)
import Data.Text.IO
import Data.Text (pack)

import Options.Applicative
import Prettyprinter.Render.Glyph

import Glyph.Abstract.Environment (Environment, Env, Name, MonadGen)
import Glyph.Interpret.Interpreter 
import Glyph.Interpret.Canonical 
import Glyph.Concrete.Internal
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

glyph_opts :: Parser Command
glyph_opts = subparser $ 
  (command "compile" $ info (CompileCommand <$> compile_opts) (progDesc "Compile a Glyph program"))
  <>
  (command "server" $ info (ServerCommand <$> server_opts) (progDesc "Launch the Glyph language server"))
  <>
  (command "interactive" $ info (InteractiveCommand <$> interactive_opts) (progDesc "Launch Glyph in interactive mode"))

main :: IO ()
main = do
  command <- execParser $ info (glyph_opts <**> helper) 
    ( fullDesc 
    <> progDesc "Compile, Run or Develop a Glyph Program"
    <> header "An implementation of the Glyph Language" )
  case command of 
    InteractiveCommand (c, backend) -> run_with_backend backend interactive c
    ServerCommand (s, backend) -> run_with_backend backend server s
    _ -> putStrLn $ pack $ show command


run_with_backend ::
  Backend
  -> (forall m e s t. (MonadError GlyphDoc m, MonadGen m, Environment Name e) =>
      (Interpreter m (e (Maybe InternalCore, InternalCore)) s t) -> a -> IO ())
  -> a -> IO ()
run_with_backend backend func val = case backend of
  Native -> func (canonical_interpreter :: Interpreter CanonM (Env (Maybe InternalCore, InternalCore)) (World InternalModule) InternalCore) val
  b -> putStrLn $ pack ("Cannot run with backend:" <> show b)
