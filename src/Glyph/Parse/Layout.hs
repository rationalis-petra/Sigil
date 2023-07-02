module Glyph.Parse.Layout () where

{----------------------------------- LAYOUTS -----------------------------------}
{- Layouts are the first phase of parsing - key syntactic structures like      -}
{- let-expressions, definitions and lambda-abstraction are parsed. However,    -}
{- mixfix expressions are left as lists of tokens. These are then parsed via   -}
{- a memoising parser in the Mixfix stage.                                     -}
{-                                                                             -}
{-------------------------------------------------------------------------------}

{------------------------------------- OLD -------------------------------------}
{----------------------------------- LAYOUTS -----------------------------------}
{- A syntax keyword can (optionally) introduce a new layout.                   -}
{- Layouts work as follows:                                                    -}
{-                                                                             -}
{- If there is an expression immediately following the keyword, all following  -}
{- expressions with the same indentation level are assigned to that keyword,   -}
{- e.g.                                                                        -}
{- do x ← read-line                                                            -}
{-    put-line $ "hi" ⋅ x                                                      -}
{-                                                                             -}
{- Alternatively, if there is no expression, the next level is assumed to have -}
{- one level of indentation deeper, e.g.                                       -}
{- do                                                                          -}
{-  x ← read-line                                                              -}
{-  put-line $ "hi" ⋅ x                                                        -}
{-                                                                             -}
{- Finally, you can place exrpressions in square (?) brackets                  -}
{- do [x ← read-line] [put-line $ "hi" ⋅ x]                                    -}
{-                                                                             -}
{-------------------------------------------------------------------------------}

{-------------------------------------------------------------------------------}
{- Syntactic macros are capable of introducing new expressions with their own  -}
{- layouts.                                                                    -}
{- Thus, the layout mechanism must be aware of syntactic macros                -}
{-                                                                             -}
{- CFG Grammar Interface                                                       -}
{- syn-do terms ≜ mdo                                                          -}
{-   m ← rule $ mkdo <$> tok 'do' <*> many1 (nest do-expr)                     -}
{-   do-expr ← dolet | dobind | expr                                           -}
{-   dolet ← mkdolet <$> tok 'let' <*> many1 (nest bind)                       -}
{-   dobind ← mkdobind <$> bind <*> tok '←' <*> (next expr)                    -}
{-                                                                             -}
{- syntax syn-do                                                               -}
{-                                                                             -}
{-                                                                             -}
{-                                                                             -}
{-                                                                             -}
{-                                                                             -}
{-------------------------------------------------------------------------------}


-- import Data.Text (Text, pack)

-- import qualified Text.Megaparsec.Char.Lexer as L
-- import Text.Megaparsec.Char
-- import Text.Megaparsec

-- import Glyph.Parse.Combinator
-- import Glyph.Parse.Lexer

-- expr :: Rules -> Grammar r (Prod r Text Token MixCore)
-- expr rules = mdo 
--   mix <- rule $ Mixfix <$>  
