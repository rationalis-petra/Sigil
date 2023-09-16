{-# OPTIONS_GHC -Wno-orphans #-}
module Sigil.Parse
  ( Range
  , Parsed
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
{-------------------------------------------------------------------------------}

-- import Debug.Trace

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
import Prettyprinter.Render.Sigil (SigilDoc)
import Prettyprinter

import Sigil.Abstract.Syntax
import Sigil.Abstract.Environment (OptBind(..), name)
import Sigil.Concrete.Decorations.Range
import Sigil.Concrete.Parsed

import Sigil.Parse.Combinator
import Sigil.Parse.Mixfix
import Sigil.Parse.Lexer

{-------------------------------- MODULE PARSER --------------------------------}
{- The module parser parses                                                    -}
{-                                                                             -}
{-------------------------------------------------------------------------------}      


-- precs_from_module :: OptBind Text ParsedCore -> Precedences
-- precs_from_module b =
update_precs_def :: Precedences -> ParsedEntry -> Precedences
update_precs_def precs def =
  case def of 
    Singleχ _ bind _ -> update_precs (maybeToList . name $ bind) precs
    Mutualχ _ mutuals -> update_precs (map (\(n,_,_) -> n) mutuals) precs
  
with_range :: ParserT m (Range -> a) -> ParserT m a
with_range p = do 
  start <- getSourcePos
  f <- p
  end <- getSourcePos
  pure $ f (Range (Just (start, end)))


-- Parase a module 
mod :: Monad m => ([Text] -> [ImportDef] -> m Precedences) -> ParserT m ParsedModule
mod get_precs = do
  (title, ports) <- module_header
  let imports = lefts ports
      exports = rights ports
  precs <- lift $ get_precs title imports

  body <-
    let go precs =
          try (do d <- L.nonIndented scn (entry precs)
                  let precs' = update_precs_def precs d
                  (d :) <$> go precs') <|> (scn *> pure [])
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


entry :: forall m. Monad m => Precedences -> ParserT m ParsedEntry
entry precs = choice' [mutual]
  where 
    mutual :: ParserT m ParsedEntry
    mutual = do
      -- TODO: parse declaration
      -- name <- anyvar
      -- _ <- symbol "⮜"
      -- tipe <- core precs
      
      args <- many1 anyvar
      _ <- symbol "≜"
      val <- core (update_precs args precs)

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


core :: forall m. Monad m => Precedences -> ParserT m ParsedCore
core precs = choice' [plam, pprod, pexpr]
  where
    plam :: ParserT m ParsedCore
    plam = 
      let unscope :: Range -> [OptBind Text ParsedCore] -> ParsedCore -> ParsedCore
          unscope range = flip $ foldr (Abs range)

          args :: ParserT m (Precedences, [OptBind Text ParsedCore])
          args = (thread1 (\(precs, args) ->
                             fmap (\a -> (update_precs (maybeToList $ name a) precs, a:args))
                                  (tyarg precs <||> arg))
                          (precs, []))

          tyarg :: Precedences -> ParserT m (OptBind Text ParsedCore)
          tyarg precs = between (symbol "(") (symbol ")") $
                    (\n t -> OptBind (Just n, Just t)) <$> anyvar <*> (symbol "⮜" *> (core precs))

          arg :: ParserT m (OptBind Text ParsedCore)
          arg =  notFollowedBy (symbol "→") *> (flip (curry OptBind) Nothing . Just  <$> anyvar)

          mklam :: ParserT m (Range -> ParsedCore)
          mklam = do
            _ <- symbol "λ"
            (precs', tel) <- args
            _ <- symbol "→"
            -- TODO: update precs per argument!!
            body <- core precs'
            pure $ \r -> unscope r (reverse tel) body

      in with_range mklam


    pprod :: ParserT m ParsedCore
    pprod = with_range mkprod
      where
        mkprod :: ParserT m (Range -> ParsedCore)
        mkprod = do
          arg <- parg <* (symbol "→")
          bdy <- core (update_precs (maybeToList $ name arg) precs)
          pure $ \r -> Prd r arg bdy

        parg :: ParserT m (OptBind Text ParsedCore)
        parg = annarg <||> ty_only

        annarg :: ParserT m (OptBind Text ParsedCore)
        annarg = between (symbol "(") (symbol ")") $
          (\n t -> OptBind (Just n, Just t)) <$> anyvar <*> (symbol "⮜" *> (core precs))

        ty_only :: ParserT m (OptBind Text ParsedCore)
        ty_only = (\t -> OptBind (Nothing, Just t)) <$> choice' [plam, pexpr]


    pexpr :: ParserT m ParsedCore
    pexpr = mixfix patom (core precs) precs
      where 
        patom = choice' [puniv]
      --   no_mixfix = choice' [plam, pprod]

    puniv :: ParserT m ParsedCore
    puniv = with_range $
      (single '𝒰' *> (flip Uni <$> subscript_int))
       <||> const (flip Uni 0) <$> symbol "𝒰"


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
