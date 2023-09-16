{-# OPTIONS_GHC -Wno-orphans #-}
module Sigil.Parse.Parse
  ( Range
  , PreMix
  , core
  , entry
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
{- This is the parser for the 'primary' grammar.                               -}
{-                                                                             -}
{-------------------------------------------------------------------------------}

-- import Debug.Trace

import Prelude hiding (head, last, tail, mod)
import Control.Monad (join)
import Control.Monad.Except (MonadError, throwError)
import qualified Data.Text as Text
import Data.Text (Text)
import Data.Either (lefts, rights)

import qualified Text.Megaparsec as Megaparsec
import qualified Text.Megaparsec.Char as C
import qualified Text.Megaparsec.Char.Lexer as L
import Text.Megaparsec hiding (runParser, parse)
import Prettyprinter.Render.Sigil (SigilDoc)
import Prettyprinter

import Sigil.Abstract.Syntax
import Sigil.Abstract.Environment (OptBind(..))
import Sigil.Concrete.Decorations.Range
import Sigil.Concrete.PreMix

import Sigil.Parse.Combinator
import Sigil.Parse.Lexer

{-------------------------------- MODULE PARSER --------------------------------}
{- The module parser parses                                                    -}
{-                                                                             -}
{-------------------------------------------------------------------------------}      


-- Parase a module 
mod :: Monad m => ParserT m PreMixModule
mod = do
  (title, ports) <- module_header
  let imports = lefts ports
      exports = rights ports

  body <- many $ L.nonIndented scn entry
      
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


entry :: forall m. Monad m => ParserT m PreMixEntry
entry = choice' [mutual]
  where 
    mutual :: ParserT m PreMixEntry
    mutual = do
      -- TODO: parse declaration
      -- name <- anyvar
      -- _ <- symbol "⮜"
      -- tipe <- core
      
      args <- many1 anyvar
      _ <- symbol "≜"
      val <- core

      let tofn [] v = v
          tofn (x:xs) v = Abs mempty (OptBind (Just x, Nothing)) (tofn xs v)

      case args of 
        [] -> error "impossible!"
        (x:xs) -> pure $ Singleχ mempty (OptBind (Just x, Nothing)) (tofn xs val)


{--------------------------------- CORE PARSER ---------------------------------}
{- The core parser first looks for the head of an expression (λ, let, etc.)    -}
{- if no identifiable head is found, then it is assumed to be a mixfix         -}
{- expression.                                                                 -}
{-------------------------------------------------------------------------------}


core :: forall m. Monad m => ParserT m PreMixCore
core = choice' [plam, pprod, pexpr]
  where

    plam :: ParserT m PreMixCore
    plam = do
      let unscope :: Range -> [OptBind Text PreMixCore] -> PreMixCore -> PreMixCore
          unscope range = flip $ foldr (Abs range)

          args :: ParserT m [OptBind Text PreMixCore]
          args = (thread1 (\(args) ->
                             fmap (:args) (tyarg <||> arg))
                          [])

          tyarg :: ParserT m (OptBind Text PreMixCore)
          tyarg = between (symbol "(") (symbol ")") $
                    (\n t -> OptBind (Just n, Just t)) <$> anyvar <*> (symbol "⮜" *> core)

          arg :: ParserT m (OptBind Text PreMixCore)
          arg =  notFollowedBy (symbol "→") *> (flip (curry OptBind) Nothing . Just  <$> anyvar)

      start <- getSourcePos
      _ <- symbol "λ"
      tel <- args
      _ <- symbol "→"
      end <- getSourcePos
      body <- core
      pure $ unscope (Range (Just (start, end))) (reverse tel) body

    pprod :: ParserT m PreMixCore
    pprod = do
        arg <- parg <* (symbol "→")
        bdy <- core
        pure $ Prd mempty arg bdy
      where
        parg :: ParserT m (OptBind Text PreMixCore)
        parg = annarg <||> ty_only

        annarg :: ParserT m (OptBind Text PreMixCore)
        annarg = between (symbol "(") (symbol ")") $
          (\n t -> OptBind (Just n, Just t)) <$> anyvar <*> (symbol "⮜" *> core)

        ty_only :: ParserT m (OptBind Text PreMixCore)
        ty_only = (\t -> OptBind (Nothing, Just t)) <$> choice' [plam, pexpr]


    pexpr :: ParserT m PreMixCore
    pexpr = choice' [puniv]
      --pmix
      --where 
      --  patom = choice' [puniv]
      --  no_mixfix = choice' [plam, pprod]

    puniv :: ParserT m PreMixCore
    puniv = do
      start <- getSourcePos
      level <- (single 'τ' *> subscript_int) <||> const 0 <$> symbol "τ"
      end <- getSourcePos
      pure $ Uni (Range (Just (start,end))) level


{------------------------------ RUNNING A PARSER -------------------------------}

parse :: MonadError SigilDoc m => ParserT m a -> Text -> Text -> m a
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
