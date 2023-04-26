module Main (main) where

import Prelude hiding (putStrLn)

import Data.Text.IO
import Data.Text (pack)

import Options.Applicative

import Interactive
import Server

data Backends = Native | JVM | Javascript | WASM
  deriving (Show, Read, Eq)

interactive_opts :: Parser InteractiveOpts
interactive_opts = InteractiveOpts
  <$> strOption
    ( long "file"
    <> short 'f'
    <> value ""
    <> help "Specify what file to run (if any)" )

data CompileOpts = CompileOpts
  { cfile :: String
  , backend :: Backends
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


server_opts :: Parser ServerOpts
server_opts = ServerOpts
  <$> option auto
    ( long "port"
    <> help "What port the server runs from"
    <> showDefault
    <> value 8801
    <> metavar "INT" )

data Command
  = InteractiveCommand InteractiveOpts
  | CompileCommand CompileOpts
  | ServerCommand ServerOpts
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
    InteractiveCommand c -> interactive c
    ServerCommand s -> server s
    _ -> putStrLn $ pack $ show command
