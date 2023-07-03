{-# OPTIONS_GHC -Wno-orphans #-}
{-# OPTIONS_GHC -Wno-unrecognised-pragmas #-}
module Glyph.Parse
  ( Range
  , Parsed
  , core
  , def
  , mod
  , runParser
  , parseToErr
  ) where


{------------------------------------ PARSER -----------------------------------}
{- The Parsing algorithm contains two distinct parts: the 'primary grammar'    -}
{- and a mixfix subgrammar. These two parts are expressed in two different     -}
{- parsers.                                                                    -}
{-                                                                             -}
{-------------------------------------------------------------------------------}


import Prelude hiding (head, last, tail, mod)
import Control.Monad (join)
import Control.Monad.Except (MonadError, throwError)
import qualified Data.Text as Text
import Data.Text (Text)
import Data.Maybe (maybeToList)

import qualified Text.Megaparsec as Megaparsec
import qualified Text.Megaparsec.Char as C
import qualified Text.Megaparsec.Char.Lexer as L
import Text.Megaparsec hiding (runParser)
import Prettyprinter

import Glyph.Abstract.Syntax
import Glyph.Abstract.Environment (OptBind(..), name)
import Glyph.Concrete.Decorations.Range
import Glyph.Concrete.Parsed

import Glyph.Parse.Combinator
import Glyph.Parse.Mixfix
import Glyph.Parse.Lexer

{-------------------------------- MODULE PARSER --------------------------------}
{- The module parser parses                                                    -}
{-                                                                             -}
{-------------------------------------------------------------------------------}      


-- precs_from_module :: OptBind Text ParsedCore -> Precedences
-- precs_from_module b =
update_precs_def :: Precedences -> ParsedDef -> Precedences
update_precs_def precs def =
  case def of 
    Mutualχ _ mutuals -> update_precs (join $ map (maybeToList . name . fst) mutuals) precs
    SigDefχ _ _ _ _ -> error "Haven't implemented update_precs_def for SigDef"
    IndDefχ _ _ _ _ -> error "Haven't implemented update_precs_def for IndDef"
  

mod :: ([PortDef] -> Precedences) -> Parser ParsedModule
mod get_precs = do
  (title, ports) <- module_header
  let imports = fmap snd . filter fst $ ports
      exports = fmap snd . filter (not . fst) $ ports
      precs = get_precs imports
  body <-
    let go precs =
          try (do d <- L.nonIndented scn (def precs)
                  let precs' = update_precs_def precs d
                  (d :) <$> (go precs')) <|> pure [] 
    in go precs
      
  pure $ Module title exports imports body

  where
    module_header :: Parser ([Text], [(Bool, PortDef)])
    module_header = do
      L.nonIndented scn (L.indentBlock scn modul)
      where 
        modul :: Parser (L.IndentOpt Parser ([Text], [(Bool, PortDef)]) [(Bool, PortDef)])
        modul = do 
          _ <- symbol "module"
          title <- sepBy anyvar (C.char '.')
          pure (L.IndentMany Nothing (pure . (title, ) . join) modulePart)
      
        modulePart :: Parser [(Bool, PortDef)]
        modulePart =
          L.indentBlock scn (imports <|> exports)
      
        imports :: Parser (L.IndentOpt Parser [(Bool, PortDef)] PortDef)
        imports = do
          _ <- symbol "import" 
          pure (L.IndentSome Nothing (pure . fmap (True,)) importStatement)
      
        importStatement :: Parser PortDef
        importStatement = fail "import statement not implemented"
          
        exports :: Parser (L.IndentOpt Parser [(Bool, PortDef)] PortDef)
        exports = do
         _ <- symbol "export"
         pure (L.IndentSome Nothing (pure . fmap (False,)) exportStatement)
      
        exportStatement :: Parser PortDef
        exportStatement = fail "export statement not implemented"

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
{-------------------------------------------------------------------------------}      


def :: Precedences -> Parser ParsedDef
def precs = choice' [mutual]
  where 
    mutual :: Parser ParsedDef
    mutual = do
      args <- many1 anyvar
      _ <- symbol "≜"
      val <- core (update_precs args precs)

      let tofn [] v = v
          tofn (x:xs) v = Abs mempty (OptBind (Just x, Nothing)) (tofn xs v)

      case args of 
        [] -> error "impossible!"
        (x:xs) -> pure $ Mutualχ mempty [(OptBind (Just x, Nothing), tofn xs val)]


{--------------------------------- CORE PARSER ---------------------------------}
{- The core parser first looks for the head of an expression (λ, let, etc.)    -}
{- if no identifiable head is found, then it is assumed to be a mixfix         -}
{- expression.                                                                 -}
{-------------------------------------------------------------------------------}


core :: Precedences -> Parser ParsedCore
core precs = choice' [plam, pprod, pexpr]
  where

    plam :: Parser ParsedCore
    plam = do
      let unscope :: [OptBind Text ParsedCore] -> ParsedCore -> ParsedCore
          unscope = flip $ foldr (Abs mempty)

          args :: Parser (Precedences, [OptBind Text ParsedCore])
          args = (thread1 (\(precs, args) ->
                             fmap (\a -> (update_precs (maybeToList $ name a) precs, a:args))
                                  (tyarg precs <||> arg))
                          (precs, []))

          tyarg :: Precedences -> Parser (OptBind Text ParsedCore)
          tyarg precs = between (symbol "(") (symbol ")") $
                    (\n t -> OptBind (Just n, Just t)) <$> anyvar <*> (symbol ":" *> (core precs))

          arg :: Parser (OptBind Text ParsedCore)
          arg =  notFollowedBy (symbol "↦") *> (flip (curry OptBind) Nothing . Just  <$> anyvar)

      _ <- symbol "λ"
      (precs', tel) <- args
      _ <- symbol "↦"
      -- TODO: update precs per argument!!
      body <- core precs'
      pure $ unscope (reverse tel) body

    pprod :: Parser ParsedCore
    pprod = do
        arg <- parg <* (symbol "→")
        bdy <- core (update_precs (maybeToList $ name arg) precs)
        pure $ Prd mempty arg bdy
      where
        parg :: Parser (OptBind Text ParsedCore)
        parg = annarg <||> ty_only

        annarg :: Parser (OptBind Text ParsedCore)
        annarg = between (symbol "(") (symbol ")") $
          (\n t -> OptBind (Just n, Just t)) <$> anyvar <*> (symbol ":" *> (core precs))

        ty_only :: Parser (OptBind Text ParsedCore)
        ty_only = (\t -> OptBind (Nothing, Just t)) <$> choice' [plam, pexpr]


    pexpr :: Parser ParsedCore
    pexpr = mixfix patom (core precs) precs
      where 
        patom = choice' [puniv]
      --   no_mixfix = choice' [plam, pprod]

    puniv :: Parser ParsedCore
    puniv = (single '𝒰' *> (Uni mempty <$> subscript_int))
      <||> (const (Uni mempty 0) <$> symbol "𝒰")


{------------------------------ RUNNING A PARSER -------------------------------}


runParser :: Parser a -> Text -> Text -> Either (Doc ann) a
runParser p file input = case Megaparsec.runParser p (Text.unpack file) input of
  Left err -> Left $ pretty $ errorBundlePretty err
  Right val -> Right val

parseToErr :: (MonadError (Doc ann) m) => Parser a -> Text -> Text -> m a
parseToErr p file input = case Megaparsec.runParser p (Text.unpack file) input of
  Left err -> throwError $ pretty $ errorBundlePretty err
  Right val -> pure val

instance ShowErrorComponent Text where 
  showErrorComponent = Text.unpack
