module Prettyprinter.Render.Glyph (GlyphStyle,
                                   GlyphDoc,
                                   Colour,
                                   putDoc,
                                   putDocLn,
                                   bold,
                                   italicized,
                                   underlined,
                                   fg_colour,
                                   bg_colour,
                                   black,
                                   red,
                                   green,
                                   yellow,
                                   blue,
                                   magenta,
                                   cyan,
                                   white,
                                   dull) where

import Prettyprinter
import qualified Prettyprinter.Render.Terminal as PPTerm


{-------------------------- GLYPH PRETTY PRINTER STYLE -------------------------}
{- This Module defines the GlyphStyle type. This style is used throughout      -}
{- Glyph in Prettyprinter docs. While not representative of a specific         -}
{- backedn, GlyphStyle Documents can be converted to a variety of backends,    -}
{- including an ANSI terminal or HTML style.                                   -}
{-------------------------------------------------------------------------------}


newtype GlyphStyle = GlyphStyle PPTerm.AnsiStyle
type GlyphDoc = Doc GlyphStyle

putDoc :: Doc GlyphStyle -> IO ()  
putDoc doc = PPTerm.putDoc (reAnnotate (\(GlyphStyle s) -> s) doc)

putDocLn :: Doc GlyphStyle -> IO ()  
putDocLn doc = putDoc doc >> putStrLn ""

bold :: GlyphStyle  
bold = GlyphStyle PPTerm.bold

italicized :: GlyphStyle  
italicized = GlyphStyle PPTerm.italicized

underlined :: GlyphStyle  
underlined = GlyphStyle PPTerm.underlined

type Colour = (Vividness, PPTerm.Color)

data Vividness = Normal | Dull

fg_colour :: Colour -> GlyphStyle
fg_colour (v, c) = GlyphStyle $ case v of 
  Normal -> PPTerm.color c
  Dull -> PPTerm.colorDull c


bg_colour :: Colour -> GlyphStyle
bg_colour (v, c) = GlyphStyle $ case v of 
  Normal -> PPTerm.bgColor c
  Dull -> PPTerm.bgColorDull c


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

        
