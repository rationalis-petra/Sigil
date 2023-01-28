module Main (main) where

import Prelude hiding (putStrLn)
import Data.Void
import Data.Text (Text)
import Data.Text.IO
import Prettyprinter
import Prettyprinter.Render.Text

import Glyph.Name
import Glyph.Core


main :: IO ()
main = putDoc doc >> (putStrLn "")
  where
    doc = pretty core

    core :: Core Name UD
    core = Abs void "x" (App void (var "x") (var "x"))

    var :: Text -> Core Name UD
    var = Var void . DeBruijn 0 

-- undecorated tree  
data UD

void :: Void  
void = error "attempt to evaluate void"

type instance Coreχ UD = Void
type instance Varχ UD = Void
type instance Prdχ UD = Void
type instance Absχ UD = Void
type instance Appχ UD = Void

instance Pretty UD where 
  pretty _ = ""
