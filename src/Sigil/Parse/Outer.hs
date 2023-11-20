{-# OPTIONS_GHC -Wno-orphans #-}
module Sigil.Parse.Outer
  ( syn_core
  , syn_entry
  , syn_mod
  ) where


{-------------------------------- OUTER PARSER ---------------------------------}
{- The Parsing algorithm contains two distinct parts: the 'outer grammar'      -}
{- and a mixfix 'inner' grammar. These two parts are expressed in two          -}
{- different parsers.                                                          -}
{-                                                                             -}
{- This file contains the 'outer grammar', which describes how to parse        -}
{- modules and various built-int constructs like functions, pattern matching   -}
{- etc. Function application is delayed, to be itself parsed via a mixfix      -}
{- subgrammar.                                                                 -}
{-------------------------------------------------------------------------------}


import Prelude hiding (head, last, tail, mod)
import Control.Monad (join)
import Control.Monad.Reader (local)
import Data.Text (Text)
import Data.Either (lefts, rights)
import Data.List.NonEmpty (NonEmpty((:|)))

import qualified Text.Megaparsec.Char as C
import qualified Text.Megaparsec.Char.Lexer as L
import Text.Megaparsec hiding (runParser, parse)

import Sigil.Abstract.Syntax
  ( ImportModifier(..), ImportDef,
    ExportModifier(..), ExportDef, Pattern(..))
import Sigil.Concrete.Decorations.Range
import Sigil.Parse.Syntax
import Sigil.Parse.Combinator
import Sigil.Parse.Lexer


with_range :: ParserT m (Range -> a) -> ParserT m a
with_range p = do 
  start <- getSourcePos
  f <- p
  end <- getSourcePos
  pure $ f (Range (Just (start, end)))

{-------------------------------- MODULE PARSER --------------------------------}
{- The module parser parses                                                    -}
{-                                                                             -}
{-------------------------------------------------------------------------------}      

syn_mod :: Monad m => ParserT m SynModule
syn_mod = do
  (title, ports) <- module_header
  let imports = lefts ports
      exports = rights ports
  body <- many $ L.nonIndented scn syn_entry
  pure $ RModule title imports exports body

  where
    module_header :: ParserT m (NonEmpty Text, [Either ImportDef ExportDef])
    module_header = do
      L.nonIndented scn (L.indentBlock scn modul)
      where 
        modul :: ParserT m (L.IndentOpt (ParserT m) (NonEmpty Text, [Either ImportDef ExportDef]) [Either ImportDef ExportDef])
        modul = do 
          symbol "module"
          title <- do
            l <- sepBy anyvar (C.char '.')
            case l of 
              (x:xs) -> pure $ x :| xs
              [] -> fail "title must be nonempty"
          pure (L.IndentMany Nothing (pure . (title, ) . join) modulePart)
      
        modulePart :: ParserT m [Either ImportDef ExportDef]
        modulePart =
          L.indentBlock scn (imports <|> exports)
      
        imports :: ParserT m (L.IndentOpt (ParserT m) [Either ImportDef ExportDef] (Either ImportDef ExportDef))
        imports = do
          symbol "import" 
          pure (L.IndentSome Nothing pure (fmap Left importStatement))
      
        importStatement :: ParserT m ImportDef
        importStatement = (,ImSingleton) . (:| []) <$> anyvar
          
        exports :: ParserT m (L.IndentOpt (ParserT m) [Either ImportDef ExportDef] (Either ImportDef ExportDef))
        exports = do
         symbol "export"
         pure (L.IndentSome Nothing pure (fmap Right exportStatement))
      
        exportStatement :: ParserT m ExportDef
        exportStatement = (,ExSingleton) . (:| []) <$> anyvar


{--------------------------------- DEF PARSER ----------------------------------}
{- The def parser parses definitions, which have one of the following forms:   -}
{- • Single definitions. These consist of a series of declarations             -}
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


syn_entry :: forall m. Monad m => ParserT m SynEntry
syn_entry = mutual
  where 
    mutual :: ParserT m SynEntry
    mutual = do
      -- TODO: parse declaration
      ann <- (do
        name <- anyvar
        symbol "⮜"
        tipe <- syn_core
        pure $ Just (name, tipe))
        <||> pure Nothing
      
      (args, val) <- L.nonIndented scn $ do
        args <- many1 anyvar
        symbol "≜"
        val <- syn_core
        pure (args, val)

      let tofn [] v = v
          tofn (x:xs) v = RAbs mempty (Just x) (Nothing) (tofn xs v)

      case args of 
        [] -> error "impossible!"
        (name : xs) -> do
          case ann of
            Just (name', _) ->
              if (name == name') then
                pure ()
              else
                fail "annotated name and definitional name must be identical"
            Nothing -> pure ()
            
          pure $ RSingle mempty name (fmap snd ann) (tofn xs val)


{--------------------------------- CORE PARSER ---------------------------------}
{- The core parser first looks for the head of an expression (λ, let, etc.)    -}
{- if no identifiable head is found, then it is assumed to be a mixfix         -}
{- expression. Current expressions are:                                        -}
{- • Lambda λ x (y ⮜ A) → e                                                    -}
{- • Product (A ⮜ 𝕌) → A → A                                                   -}
{- • Universe 𝕌 | 𝕌ₙ                                                           -}
{- • Identity Id (x ⮜ A = e) (y ⮜ B = e'). A e e                               -}
{- • Id-App   Ap (x ⮜ A = e) (y ⮜ B = e'). e                                   -}
{-                                                                             -}
{-------------------------------------------------------------------------------}


syn_core :: forall m. Monad m => ParserT m Syntax
syn_core = do
  next <- lookAhead (satisfy (const True))
  case next of
    'λ' -> plam
    'ι' -> pid
    'ρ' -> pap
    'μ' -> pind
    'φ' -> prec
    _ -> pprod <||> pexpr
  where
    plam :: ParserT m Syntax
    plam = 
      let unscope :: Range -> [(Maybe Text, Maybe Syntax)] -> Syntax -> Syntax
          unscope range = flip $ foldl (flip . uncurry $ RAbs range)

          args :: ParserT m [(Maybe Text, Maybe Syntax)]
          args = many (tyarg <||> arg)

          tyarg :: ParserT m (Maybe Text, Maybe Syntax)
          tyarg = between lparen rparen $
                    (\n t -> (Just n, Just t)) <$> anyvar <*> (symbol "⮜" *> syn_core)

          arg :: ParserT m (Maybe Text, Maybe Syntax)
          arg =  notFollowedBy (symbol "→") *> ((,Nothing) . Just <$> anyvar)

          mklam :: ParserT m (Range -> Syntax)
          mklam = do
            symbol "λ"
            tel <- args
            symbol "→"
            body <- syn_core
            pure $ \r -> unscope r (reverse tel) body

      in with_range mklam


    pprod :: ParserT m Syntax
    pprod = with_range mkprod
      where
        mkprod :: ParserT m (Range -> Syntax)
        mkprod = do
          (mn, mty) <- parg <* (symbol "→")
          bdy <- syn_core
          pure $ \r -> RPrd r mn mty bdy

        parg :: ParserT m (Maybe Text, Maybe Syntax)
        parg = annarg <||> ty_only

        annarg :: ParserT m (Maybe Text, Maybe Syntax)
        annarg = between lparen rparen $
          (\l r -> (Just l, Just r)) <$> anyvar <*> (symbol "⮜" *> syn_core)

        ty_only :: ParserT m (Maybe Text, Maybe Syntax)
        ty_only = (\t -> (Nothing, Just t)) <$> choice' [plam, pexpr]


    pid :: ParserT m Syntax
    pid = with_range mkid 
      where
        mkid :: ParserT m (Range -> Syntax)
        mkid = do 
          symbol "ι"
          tel <- ptel
          symbol "."
          RMix _ [ty, a, a'] <- syn_core
          let syn = \case 
                NamePart txt -> RMix mempty [NamePart txt]
                Syn core -> core
          pure $ (\r -> REql r tel (syn ty) (syn a) (syn a'))

    pap :: ParserT m Syntax
    pap = with_range mkap 
      where
        mkap :: ParserT m (Range -> Syntax)
        mkap = do 
          symbol "ρ"
          tel <- ptel
          symbol "."
          pf <- syn_core
          pure $ (\r -> RDap r tel pf)

    ptel :: ParserT m RawTel
    ptel =
      (do
        entry <- between lparen rparen $ do
          arg <- fmap Just anyvar
          ty <- syn_core
          (v1, v2) <- between lparen rparen $ do
            v1 <- syn_core
            symbol "="
            v2 <- syn_core
            pure (v1, v2)
          symbol "≜"
          id <- syn_core
          pure (arg, (Just (ty, v1, v2)), id)
        tel' <- ptel
        pure $ entry : tel')
      <||> pure []
            
    pind :: ParserT m Syntax
    pind = mkind --with_range (mkind)
      where 
        mkind :: ParserT m Syntax
        mkind = L.indentBlock scn $ do
          symbol "μ"
          var <- anyvar 
          symbol "⮜"
          ty <- syn_core
          symbol "."
          pctors var ty

        pctors :: Text -> Syntax -> ParserT m (L.IndentOpt (ParserT m) Syntax (Text, Syntax))
        pctors var ty = do
          pure (L.IndentMany Nothing (pure . (RInd mempty var (Just ty))) pctor)

        pctor :: ParserT m (Text, Syntax)
        pctor = do
          var <- anyvar
          symbol "⮜"
          (var, ) <$> syn_core
          

    prec :: ParserT m Syntax
    prec = mkrec
      where 
        mkrec = L.indentBlock scn $ do
          symbol "φ"
          var <- anyvar
          symbol "⮜"
          ty <- syn_core
          symbol ","
          val <- syn_core
          symbol "."
          pcases var ty val

        pcases var ty val =
          pure $ (L.IndentMany Nothing (pure . RRec mempty (Just var) (Just ty) val) pcase)

        pcase = do
          pat <- ppattern 
          symbol "→"
          (pat,) <$> syn_core

        ppattern :: ParserT m (Pattern Text)
        ppattern = do 
          level <- L.indentLevel
          local (const $ level) $
            (PatCtr <$> (single ':' *> anyvar) <*> many ppattern)
            <|> (PatVar <$> (try $ anyvar >>= (\v -> if (v == "→") then fail "ppattern" else pure v)))
        

    pexpr :: ParserT m Syntax
    pexpr = do
        RMix mempty <$>
          (many1 $ Syn <$> (between lparen rparen syn_core <|> patom)
                   <|> NamePart <$> anyvar)
      where 
        patom = puniv <|> pctor

    puniv :: ParserT m Syntax
    puniv = with_range $
      (single '𝕌' *> (flip RUni <$> subscript_int))
       <||> const (flip RUni 0) <$> symbol "𝕌"
    pctor :: ParserT m Syntax
    pctor = with_range $ do
      label <- (single ':' *> anyvar)
      tipe <- (Just <$> try (single '﹨' *> sc *> syn_core)) <|> pure Nothing
      pure $ \r -> RCtr r label tipe
