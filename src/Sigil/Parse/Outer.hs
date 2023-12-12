{-# OPTIONS_GHC -Wno-orphans #-}
module Sigil.Parse.Outer
  ( syn_core
  , syn_entry
  , syn_mod
  , syn_formula
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
import Data.Text (Text)
import Data.Either (lefts, rights)
import Data.List.NonEmpty (NonEmpty((:|)))

import qualified Text.Megaparsec.Char as C
import qualified Text.Megaparsec.Char.Lexer as L
import Text.Megaparsec hiding (runParser, parse)

import Sigil.Abstract.Names ( Path(..) )
import Sigil.Abstract.Unify
import Sigil.Abstract.Syntax
  ( ImportModifier(..), ImportDef(..),
    ExportModifier(..), ExportDef(..), Pattern(..) )
import Sigil.Concrete.Decorations.Range
import Sigil.Concrete.Decorations.Implicit
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
  body <- many $ L.nonIndented scn (syn_entry <* scn)
  pure $ RModule title imports exports body

  where
    module_header :: ParserT m (Path, [Either ImportDef ExportDef])
    module_header = do
      L.nonIndented scn (L.indentBlock scn modul)
      where 
        modul :: ParserT m (L.IndentOpt (ParserT m) (Path, [Either ImportDef ExportDef]) [Either ImportDef ExportDef])
        modul = do 
          symbol "module"
          title <- do
            l <- sepBy anyvar (C.char '.')
            case l of 
              (x:xs) -> pure $ Path $ x :| xs
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
        importStatement = Im . (,ImSingleton) . Path . (:| []) <$> anyvar
          
        exports :: ParserT m (L.IndentOpt (ParserT m) [Either ImportDef ExportDef] (Either ImportDef ExportDef))
        exports = do
         symbol "export"
         pure (L.IndentSome Nothing pure (fmap Right exportStatement))
      
        exportStatement :: ParserT m ExportDef
        exportStatement = Ex . (,ExSingleton) . Path . (:| []) <$> anyvar


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
      level <- L.indentLevel 
      -- TODO: parse declaration
      ann <- (do
        name <- anyvar
        symbol "⮜"
        tipe <- syn_core level
        pure $ Just (name, tipe))
        <||> pure Nothing
      
      let tofn [] v = v
          tofn ((at, x):xs) v = RAbs mempty at (Just x) (Nothing) (tofn xs v)

      (name, def) <- L.nonIndented scn $ do
        name <- anyvar
        args <- many (((Regular,) <$> anyvar) <||> between langle rangle ((Implicit,) <$> anyvar))
        symbol "≜"
        val <- syn_core level
        let def =  RSingle mempty name (fmap snd ann) (tofn args val)
        pure (name, def)

      case ann of
        Just (name', _) ->
          if (name == name') then
            pure ()
          else
            fail "annotated name and definitional name must be identical"
        Nothing -> pure ()
           
      pure $ def


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


syn_core :: forall m. Monad m => Pos -> ParserT m Syntax
syn_core level = do
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
      let unscope :: Range -> [(ArgType, Maybe Text, Maybe Syntax)] -> Syntax -> Syntax
          unscope range = flip $ foldl (\body (aty, mt, ms) -> RAbs range aty mt ms body)

          args :: ParserT m [(ArgType, Maybe Text, Maybe Syntax)]
          args = many (tyarg <||> arg)

          tyarg :: ParserT m (ArgType, Maybe Text, Maybe Syntax)
          tyarg = (between lparen rparen $
                   (\n t -> (Regular, Just n, Just t)) <$> anyvar <*> (symbol "⮜" *> syn_core level))
                  <||> (between langle rangle $
                        (\n t -> (Implicit, Just n, Just t)) <$> anyvar <*> (symbol "⮜" *> syn_core level))

          arg :: ParserT m (ArgType, Maybe Text, Maybe Syntax)
          arg = notFollowedBy (symbol "→") *>
            (((Regular,,Nothing) . Just <$> anyvar) <||> between langle rangle ((Implicit,,Nothing) . Just <$> anyvar))

          mklam :: ParserT m (Range -> Syntax)
          mklam = do
            symbol "λ"
            tel <- args
            symbol "→"
            body <- syn_core level
            pure $ \r -> unscope r (reverse tel) body

      in with_range mklam


    pprod :: ParserT m Syntax
    pprod = with_range mkprod
      where
        mkprod :: ParserT m (Range -> Syntax)
        mkprod = do
          (at, mn, mty) <- parg <* (symbol "→")
          bdy <- syn_core level
          pure $ \r -> RPrd r at mn mty bdy

        parg :: ParserT m (ArgType, Maybe Text, Maybe Syntax)
        parg = annarg <||> ty_only

        annarg :: ParserT m (ArgType, Maybe Text, Maybe Syntax)
        annarg = (between lparen rparen $
                  (\l r -> (Regular, Just l, Just r)) <$> anyvar <*> (symbol "⮜" *> syn_core level))
                 <||> (between langle rangle $
                       (\l r -> (Implicit, Just l, Just r)) <$> anyvar <*> (symbol "⮜" *> syn_core level))

        ty_only :: ParserT m (ArgType, Maybe Text, Maybe Syntax)
        ty_only = (\t -> (Regular, Nothing, Just t)) <$> choice' [plam, pexpr]


    pid :: ParserT m Syntax
    pid = with_range mkid 
      where
        mkid :: ParserT m (Range -> Syntax)
        mkid = do 
          symbol "ι"
          tel <- ptel
          symbol "."
          RMix _ [ty, a, a'] <- syn_core level
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
          pf <- syn_core level
          pure $ (\r -> RDap r tel pf)

    ptel :: ParserT m RawTel
    ptel =
      (do
        entry <- between lparen rparen $ do
          arg <- fmap Just anyvar
          ty <- syn_core level
          (v1, v2) <- between lparen rparen $ do
            v1 <- syn_core level
            symbol "="
            v2 <- syn_core level
            pure (v1, v2)
          symbol "≜"
          id <- syn_core level
          pure (arg, (Just (ty, v1, v2)), id)
        tel' <- ptel
        pure $ entry : tel')
      <||> pure []
            
    pind :: ParserT m Syntax
    pind = mkind --with_range (mkind)
      where 
        mkind :: ParserT m Syntax
        mkind = do
          symbol "μ"
          var <- anyvar 
          symbol "⮜"
          ty <- syn_core level
          symbol "."
          ctors <- many $ try pctor
          pure $ RInd mempty var (Just ty) ctors

        pctor :: ParserT m (Text, Syntax)
        pctor = do
          level' <- L.indentGuard scn GT level
          var <- anyvar
          symbol "⮜"
          (var, ) <$> syn_core level'
          

    prec :: ParserT m Syntax
    prec = mkrec
      where 
        mkrec = do
          symbol "φ"
          var <- anyvar
          symbol "⮜"
          ty <- syn_core level
          symbol ","
          val <- syn_core level
          symbol "."
          cases <- many $ try pcase
          pure $ RRec mempty (Just var) (Just ty) val cases

        pcase = do
          level' <- L.indentGuard scn GT level
          pat <- ppattern 
          symbol "→"
          (pat,) <$> syn_core level'

        ppattern :: ParserT m (Pattern Text)
        ppattern =
          (PatCtr <$> (single ':' *> anyvar) <*> many ppattern)
          <|> (PatVar <$> (try $ anyvar >>= (\v -> if (v == "→") then fail "ppattern" else pure v)))
        

    pexpr :: ParserT m Syntax
    pexpr = do
        RMix mempty <$>
          (many1 $ Syn <$> (between lparen rparen (syn_core level) <|> patom)
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
      tipe <- (Just <$> try (single '﹨' *> sc *> syn_core level)) <|> pure Nothing
      pure $ \r -> RCtr r label tipe


{------------------------------- FORMULA PARSER --------------------------------}
{- The Formula parser parses unification formulas, which have several nodes:   -}
{- • Forall: ∀ x ⮜ core. formula                                               -}
{- • Exists: ∃ x ⮜ core. formula                                               -}
{- • Conjugation: formula ∧ formula'                                           -}
{- • Equality: core ≃ core'                                                    -}
{- • Has-type: core ∈ core'                                                    -}
{-                                                                             -}
{-------------------------------------------------------------------------------}

syn_formula :: forall m. Monad m => Pos -> ParserT m (Formula Text Syntax)
syn_formula level = do
  next <- lookAhead (satisfy (const True))
  case next of
    '∃' -> pbind "∃" Exists
    '∀' -> pbind "∀" Forall
    '(' -> pconj
    _ -> psingles

  where
    pbind :: Text -> Quant -> ParserT m (Formula Text Syntax)
    pbind sym quant = do
      symbol sym
      var <- anyvar
      symbol "⮜"
      ty <- syn_core level
      symbol "."
      formula <- syn_formula level
      pure $ Bind quant var ty formula

    pconj :: ParserT m (Formula Text Syntax)
    pconj = do
      fm₁ <- between lparen rparen $ syn_formula level
      symbol "∧"
      fm₂ <- between lparen rparen $ syn_formula level
      pure $ And fm₁ fm₂

    psingles :: ParserT m (Formula Text Syntax)
    psingles = do
      fs <- sepBy psingle (symbol "∧")
      case fs of 
        (_:_)  -> pure $ Conj fs
        _ -> fail "Can't have empty conjgation"

    psingle :: ParserT m (SingleConstraint Syntax)
    psingle = do
      core₁ <- syn_core level
      f <- (const (:≗:) <$> symbol "≃") <|> (const (:∈:) <$> symbol "∈")
      core₂ <- syn_core level
      pure $ f core₁ core₂

