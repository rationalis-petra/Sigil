module Glyph.Parse
  ( Range
  , Parsed
  , core
  , def
  , runParser
  , parseToErr
  ) where

{------------------------------------ PARSER -----------------------------------}
{- The Parsing algorithm contains two distinct parts: the 'primary grammar'    -}
{- and a mixfix subgrammar. These two parts are expressed in two different     -}
{- parsers.                                                                    -}
{-                                                                             -}
{-------------------------------------------------------------------------------}


import Prelude hiding (head, last, tail)
import Control.Monad.Except (MonadError, throwError)
import qualified Data.Text as Text
import Data.Text (Text)

import qualified Text.Megaparsec as Megaparsec
import Text.Megaparsec hiding (runParser)
import Prettyprinter

import Glyph.Abstract.Syntax
import Glyph.Abstract.Environment (OptBind(..))
import Glyph.Concrete.Decorations.Range
import Glyph.Concrete.Parsed

import Glyph.Parse.Combinator
import Glyph.Parse.Mixfix
import Glyph.Parse.Lexer


{--------------------------------- DEF PARSER ----------------------------------}
{- The def parser parses definitions, which have one of the following forms:   -}
{- • Single/Mutual definitions. These consist of a series of declarations      -}
{-   (var : expr) followed by a series of definitions (var arg* ≜ expr)        -}
{-   in which any declared name is in scope. For example:                      -}
{-                                                                             -}
{-   v1 : A → B → C                                                            -}
{-   v2 : A → A → B → C                                                        -}
{-                                                                             -}
{-   v1 a b ≜ v2 a a b                                                         -}
{-   v2 a a b ≜ ∨1 a b                                                         -}
{-                                                                             -}
{-   If there is only one declaration, then it is a single definition, as it   -}
{-   is not mutually recursive, but this is a special case.                    -}
{-                                                                             -}
{- •                                                                           -}
{-------------------------------------------------------------------------------}      


def :: Precedences -> Parser RawDefinition
def precs = choice [mutual]
  where 
    mutual :: Parser RawDefinition
    mutual = do
      args <- many1 anyvar
      _ <- symbol "≜"
      val <- core (update_precs args precs)

      let tofn [] v = v
          tofn (x:xs) v = Abs mempty (OptBind $ Left x) (tofn xs v)

      case args of 
        [] -> error "impossible!"
        (x:xs) -> pure $ Mutual [(OptBind $ Left x, tofn xs val)]


{--------------------------------- CORE PARSER ---------------------------------}
{- The core parser first looks for the head of an expression (λ, let, etc.)    -}
{- if no identifiable head is found, then it is assumed to be a mixfix         -}
{- expression.                                                                 -}
{-------------------------------------------------------------------------------}      


core :: Precedences -> Parser RawCore
core precs = choice [plam, pexpr]
  where
    plam :: Parser RawCore
    plam = do
      let unscope :: [Text] -> RawCore -> RawCore
          unscope = flip $ foldr (\v rest -> Abs mempty (OptBind $ Left v) rest)

          args :: Parser [Text]
          args = between (symbol "[") (symbol "]") (many1 arg)  

          arg :: Parser Text
          arg = anyvar

      _ <- symbol "λ"
      tel <- args

      body <- core (update_precs tel precs)
      pure $ unscope tel body

    pexpr :: Parser RawCore
    pexpr = run_precs precs (mixfix no_mixfix)
      where 
        no_mixfix = choice [plam]


    -- buildapp [] = fail "empty buildapp"
    -- buildapp (x:xs) = pure $ foldl' (App mempty) x xs

{------------------------------ RUNNING A PARSER -------------------------------}


runParser :: Parser a -> Text -> Text -> Either Text a
runParser p file input = case Megaparsec.runParser p (Text.unpack file) input of
  Left err -> Left $ Text.pack $ show $ err
  Right val -> Right val

parseToErr :: (MonadError (Doc ann) m) => Parser a -> Text -> Text -> m a
parseToErr p file input = case Megaparsec.runParser p (Text.unpack file) input of
  Left err -> throwError $ pretty $ show err
  Right val -> pure val
