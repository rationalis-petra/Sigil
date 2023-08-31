{-# OPTIONS_GHC -Wno-orphans #-}
module Glyph.Parse
  ( Range
  , Parsed
  , core
  , def
  , mod
  , parse
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
import Control.Monad.Trans (lift)
import Control.Monad.Except (MonadError, throwError)
import qualified Data.Text as Text
import Data.Text (Text)
import Data.Either (lefts, rights)
import Data.Maybe (maybeToList)

import qualified Text.Megaparsec as Megaparsec
import qualified Text.Megaparsec.Char as C
import qualified Text.Megaparsec.Char.Lexer as L
import Text.Megaparsec hiding (runParser, parse)
import Prettyprinter.Render.Glyph (GlyphDoc)
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
  

-- Parase a module 
mod :: Monad m => ([Text] -> [ImportDef] -> m Precedences) -> ParserT m ParsedModule
mod get_precs = do
  (title, ports) <- module_header
  let imports = lefts ports
      exports = rights ports
  precs <- lift $ get_precs title imports

  body <-
    let go precs =
          try (do d <- L.nonIndented scn (def precs)
                  let precs' = update_precs_def precs d
                  (d :) <$> go precs') <|> pure [] 
    in go precs
      
  pure $ Module title imports exports body

  where
    module_header :: ParserT m ([Text], [Either ImportDef ExportDef])
    module_header = do
      L.nonIndented scn (L.indentBlock scn modul)
      where 
        modul :: ParserT m (L.IndentOpt (ParserT m) ([Text], [Either ImportDef ExportDef]) [Either ImportDef ExportDef])
        modul = do 
          _ <- symbol "module"
          title <- sepBy anyvar (C.char '.')
          pure (L.IndentMany Nothing (pure . (title, ) . join) modulePart)
      
        modulePart :: ParserT m [Either ImportDef ExportDef]
        modulePart =
          L.indentBlock scn (imports <|> exports)
      
        imports :: ParserT m (L.IndentOpt (ParserT m) [Either ImportDef ExportDef] (Either ImportDef ExportDef))
        imports = do
          _ <- symbol "import" 
          pure (L.IndentSome Nothing pure (fmap Left importStatement))
      
        importStatement :: ParserT m ImportDef
        importStatement = fail "import statement not implemented"
          
        exports :: ParserT m (L.IndentOpt (ParserT m) [Either ImportDef ExportDef] (Either ImportDef ExportDef))
        exports = do
         _ <- symbol "export"
         pure (L.IndentSome Nothing pure (fmap Right exportStatement))
      
        exportStatement :: ParserT m ExportDef
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


def :: forall m. Monad m => Precedences -> ParserT m ParsedDef
def precs = choice' [mutual]
  where 
    mutual :: ParserT m ParsedDef
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


core :: forall m. Monad m => Precedences -> ParserT m ParsedCore
core precs = choice' [plam, pprod, pexpr]
  where

    plam :: ParserT m ParsedCore
    plam = do
      let unscope :: [OptBind Text ParsedCore] -> ParsedCore -> ParsedCore
          unscope = flip $ foldr (Abs mempty)

          args :: ParserT m (Precedences, [OptBind Text ParsedCore])
          args = (thread1 (\(precs, args) ->
                             fmap (\a -> (update_precs (maybeToList $ name a) precs, a:args))
                                  (tyarg precs <||> arg))
                          (precs, []))

          tyarg :: Precedences -> ParserT m (OptBind Text ParsedCore)
          tyarg precs = between (symbol "(") (symbol ")") $
                    (\n t -> OptBind (Just n, Just t)) <$> anyvar <*> (symbol ":" *> (core precs))

          arg :: ParserT m (OptBind Text ParsedCore)
          arg =  notFollowedBy (symbol "→") *> (flip (curry OptBind) Nothing . Just  <$> anyvar)

      _ <- symbol "λ"
      (precs', tel) <- args
      _ <- symbol "→"
      -- TODO: update precs per argument!!
      body <- core precs'
      pure $ unscope (reverse tel) body

    pprod :: ParserT m ParsedCore
    pprod = do
        arg <- parg <* (symbol "→")
        bdy <- core (update_precs (maybeToList $ name arg) precs)
        pure $ Prd mempty arg bdy
      where
        parg :: ParserT m (OptBind Text ParsedCore)
        parg = annarg <||> ty_only

        annarg :: ParserT m (OptBind Text ParsedCore)
        annarg = between (symbol "(") (symbol ")") $
          (\n t -> OptBind (Just n, Just t)) <$> anyvar <*> (symbol ":" *> (core precs))

        ty_only :: ParserT m (OptBind Text ParsedCore)
        ty_only = (\t -> OptBind (Nothing, Just t)) <$> choice' [plam, pexpr]


    pexpr :: ParserT m ParsedCore
    pexpr = mixfix patom (core precs) precs
      where 
        patom = choice' [puniv]
      --   no_mixfix = choice' [plam, pprod]

    puniv :: ParserT m ParsedCore
    puniv = (single '𝒰' *> (Uni mempty <$> subscript_int))
      <||> const (Uni mempty 0) <$> symbol "𝒰"


{------------------------------ RUNNING A PARSER -------------------------------}

parse :: MonadError GlyphDoc m => ParserT m a -> Text -> Text -> m a
parse p file input = do
  result <- Megaparsec.runParserT p (Text.unpack file) input 
  case result of 
    Left err -> throwError $ pretty $ errorBundlePretty err
    Right val -> pure val

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
