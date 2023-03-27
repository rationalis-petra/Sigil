module Main (main) where

import Prelude hiding (putStrLn)

--import Data.Semigroup ((<>))
import Data.Text.IO

-- import Prettyprinter.Render.Text
-- import Options.Applicative

-- data Backends = Native | JVM | Javascript | WASM

-- data InteractiveOpts = InteractiveOpts
--   { ifile :: String
--   }

-- interactive_ops :: Parser InteractiveOpts
-- interactive_ops = InteractiveOpts <$>
--   <$> 

-- data CompileOpts = CompileOpts
--   { cfile :: String
--   , backend
--   }

-- compile_ops :: Parser CompileOpts
-- compile_ops = CompileOpts <$>

-- data ServerOpts = ServerOpts
--   { port :: Int
--   }

-- server_ops :: Parser ServerOpts
-- server_ops = ServerOpts <$>

-- data Command = InteractiveCommand | CompileCommand | ServerCommand

  

-- glyph_opts :: Parser Command
-- glyph_opts = subparser $ 
--   (command "compile" $ info compile_opts (progDesc ""))
--   <>
--   (command "serve" $ info serve_opts (progDesc ""))
--   <>
--   (command "interactive" $ info interactive_opts (progDesc ""))

main :: IO ()
main = putStrLn "Hello, World!" -- execParser glyph_opts
