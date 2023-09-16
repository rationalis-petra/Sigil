module Prettyprinter.Render.Sigil
  ( SigilPretty(..)
  , SigilStyle
  , SigilDoc
  , Colour
  , putDoc
  , putDocLn
  , bold
  , italicized
  , underlined
  , fg_colour
  , bg_colour
  , black
  , red
  , green
  , yellow
  , blue
  , magenta
  , cyan
  , white
  , dull ) where


{-------------------------- Sigil. PRETTY PRINTER STYLE -------------------------}
{- This Module defines the SigilStyle type. This style is used throughout      -}
{- Sigil. in Prettyprinter docs. While not representative of a specific         -}
{- backedn, SigilStyle Documents can be converted to a variety of backends,    -}
{- including an ANSI terminal or HTML style.                                   -}
{-------------------------------------------------------------------------------}


import Prettyprinter
import qualified Prettyprinter.Render.Terminal as PPTerm


{------------------------------------ TYPES ------------------------------------}


newtype SigilStyle = SigilStyle PPTerm.AnsiStyle
type SigilDoc = Doc SigilStyle

type Colour = (Vividness, PPTerm.Color)
data Vividness = Normal | Dull

class SigilPretty a where  
  spretty :: a -> SigilDoc 


{---------------------------------- RENDERING ----------------------------------}


putDoc :: Doc SigilStyle -> IO ()  
putDoc doc = PPTerm.putDoc (reAnnotate (\(SigilStyle s) -> s) doc)

putDocLn :: Doc SigilStyle -> IO ()  
putDocLn doc = putDoc doc >> putStrLn ""


{-------------------------------- CREATE STYLES --------------------------------}


bold :: SigilStyle  
bold = SigilStyle PPTerm.bold

italicized :: SigilStyle  
italicized = SigilStyle PPTerm.italicized

underlined :: SigilStyle  
underlined = SigilStyle PPTerm.underlined

fg_colour :: Colour -> SigilStyle
fg_colour (v, c) = SigilStyle $ case v of 
  Normal -> PPTerm.color c
  Dull -> PPTerm.colorDull c

bg_colour :: Colour -> SigilStyle
bg_colour (v, c) = SigilStyle $ case v of 
  Normal -> PPTerm.bgColor c
  Dull -> PPTerm.bgColorDull c

{----------------------------------- COLOURS -----------------------------------}

black   :: Colour
black   = (Normal, PPTerm.Black)

red     :: Colour
red     = (Normal, PPTerm.Red)

green   :: Colour
green   = (Normal, PPTerm.Green)

yellow  :: Colour
yellow  = (Normal, PPTerm.Yellow)

blue    :: Colour
blue    = (Normal, PPTerm.Blue)

magenta :: Colour
magenta = (Normal, PPTerm.Magenta)

cyan    :: Colour
cyan    = (Normal, PPTerm.Cyan)

white   :: Colour
white   = (Normal, PPTerm.White)

dull :: Colour -> Colour
dull (_, c) = (Dull, c) 

        
