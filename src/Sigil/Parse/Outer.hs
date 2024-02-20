{-# OPTIONS_GHC -Wno-orphans #-}
module Sigil.Parse.Outer
  ( syn_core
  , syn_entry
  , syn_mod
  , mod_header
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
import qualified Data.Set as Set
import Data.Text (Text)
import Data.Either (lefts, rights)
import Data.List.NonEmpty (NonEmpty((:|)))

import qualified Text.Megaparsec.Char as C
import qualified Text.Megaparsec.Char.Lexer as L
import Text.Megaparsec hiding (runParser, parse)

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

mod_header :: ParserT m (NonEmpty Text, [Either ImportDef ExportDef])
mod_header = L.nonIndented scn (L.indentBlock scn modul)
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
    importStatement = do
      var <- anyvar
      vars <- many (try $ C.char '.' *> anyvar)
      choice' [ (symbol ".(…)" *> (pure $ Im $ (,ImWildcard) $ var :| vars))
              , (do set <- Set.fromList <$> (C.char '.' *> between lparen rparen (many1 anyvar))
                    pure $ Im $ (,ImGroup set) $ var :| vars)
              , pure $ Im $ (,ImSingleton) $ var :| vars
              ]

      
    exports :: ParserT m (L.IndentOpt (ParserT m) [Either ImportDef ExportDef] (Either ImportDef ExportDef))
    exports = do
     symbol "export"
     pure (L.IndentSome Nothing pure (fmap Right exportStatement))
    
    exportStatement :: ParserT m ExportDef
    exportStatement = Ex . (,ExSingleton) . (:| []) <$> anyvar

syn_mod :: Monad m => ParserT m SynModule
syn_mod = do
  (title, ports) <- mod_header
  let imports = lefts ports
      exports = rights ports
  body <- many $ L.nonIndented scn (syn_entry <* scn)
  pure $ RModule title imports exports body

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

      let tofn _ [] v = v
          tofn r ((at, x, r'):xs) v = RAbs (r <> r') at (Just x) (Nothing) (tofn r xs v)

      (name, def) <- L.nonIndented scn $ do
        start <- getSourcePos
        name <- anyvar
        args <- many $ with_range (((Regular,,) <$> anyvar) <||> between langle rangle ((Implicit,,) <$> anyvar))
        symbol "≜"
        val <- syn_core level
        end <- getSourcePos
        let def = RSingle (Range (Just (start, end))) name (fmap snd ann) (tofn (range val) args val)
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
{- • Identity Id (x ⮜ A ≜ e) (y ⮜ B ≜ e'). A e e                               -}
{- • Id-App   Ap (x ⮜ A ≜ e) (y ⮜ B ≜ e'). e                                   -}
{-                                                                             -}
{-------------------------------------------------------------------------------}


syn_core :: forall m. Monad m => Pos -> ParserT m Syntax
syn_core level = do
  next <- lookAhead (satisfy (const True))
  val <- case next of
    'λ' -> plam
    'μ' -> pind
    'φ' -> prec
    'ι' -> pid
    'ρ' -> pap
    '⍃' -> (ptr RTrL)
    '⍄' -> (ptr RTrR)
    '⎕' -> ptr =<< ((symbol "⎕⍄" *> pure RLfR) <||> (symbol "⎕⍃" *> pure RLfL))
    _ -> pprod <||> pexpr
  f <- (symbol "↓" *> pure (\v -> RETC (range v) v))
       <||> (symbol "↑" *> pure (\v -> RCTE (range v) v))
       <||> pure id 
  pure $ f val
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
            
    pind :: ParserT m Syntax
    pind = with_range mkind
      where 
        mkind :: ParserT m (Range -> Syntax)
        mkind = do
          symbol "μ"
          var <- anyvar 
          symbol "⮜"
          ty <- syn_core level
          symbol "."
          ctors <- many $ try pctor
          pure $ \r -> RInd r var (Just ty) ctors

        pctor :: ParserT m (Text, Syntax)
        pctor = do
          level' <- L.indentGuard scn GT level
          var <- anyvar
          symbol "⮜"
          (var, ) <$> syn_core level'
          

    prec :: ParserT m Syntax
    prec = with_range mkrec
      where 
        mkrec = do
          symbol "φ"
          res <- (do var <- anyvar
                     symbol "⮜"
                     ty <- syn_core level
                     symbol ","
                     pure $ Just (var, ty))
                 <||> pure Nothing
          val <- syn_core level
          symbol "."
          cases <- many $ try pcase
          pure $ \r -> RRec r (fmap fst res) (fmap snd res) val cases

        pcase = do
          level' <- L.indentGuard scn GT level
          pat <- ppattern 
          symbol "→"
          (pat,) <$> syn_core level'

        ppattern :: ParserT m (Pattern Text)
        ppattern =
          (PatCtr <$> (single ':' *> anyvar) <*> many ppattern)
          <|> (PatVar <$> (try $ anyvar >>= (\v -> if (v == "→") then fail "ppattern" else pure v)))

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
                NamePart r txt -> RMix r [NamePart r txt]
                Syn _ core -> core -- TODO: report error on implicit?
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

    ptr :: (Range -> RawTel -> Syntax -> Syntax -> Syntax) -> ParserT m Syntax
    ptr f = with_range mktr
      where
        mktr = do 
          symbol "⎕" <|> symbol "⍄" <|> symbol "⍃"
          tel <- ptel
          symbol "."
          RMix _ [ty, val] <- syn_core level
          let syn = \case 
                NamePart r txt -> RMix r [NamePart r txt]
                Syn _ core -> core -- TODO: report error on implicit?
          pure $ \r -> f r tel (syn ty) (syn val)

    ptel :: ParserT m RawTel
    ptel =
      (do
        entry <- between lparen rparen $ do
          arg <- fmap Just anyvar
          next <- lookAhead (satisfy (const True))
          case next of
            '⮜' -> do
              symbol "⮜"
              RMix _ [ty, a, a'] <- syn_core level
              symbol "≜"
              val <- syn_core level
              let syn = \case
                    NamePart r txt -> RMix r [NamePart r txt]
                    Syn _ core -> core -- TODO: report error on implicit?
              pure (arg, Just (syn ty, syn a, syn a'), val)
            '≜' -> do
              symbol "≜"
              val <- syn_core level
              pure (arg, Nothing, val)
            _ -> fail "expecting telescope ⮜ or ≜"
        tel' <- ptel
        pure $ entry : tel')
      <||> pure []
        

    pexpr :: ParserT m Syntax
    pexpr = with_range mkmix 
      where 
        mkmix :: ParserT m (Range -> Syntax)
        mkmix = flip RMix <$> many1 mix_token

        mix_token :: ParserT m (MixToken Syntax)
        mix_token = (Syn Regular <$> (between lparen rparen (syn_core level) <|> patom))
          <|> (Syn Regular <$> (between langle rangle (syn_core level) <|> patom))
          <|> with_range (flip NamePart <$> anyvar)

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
{- • Conjugation: (formula) ∧ (formula')                                       -}
{- • Equality: core ≅ core'                                                    -}
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
      forms <- sepBy (between lparen rparen $ syn_formula level) (symbol "⩑" )
      case reverse forms of 
        (f : fs) -> pure $ foldr And f fs
        _ -> fail "empty formula conjugation"

    psingles :: ParserT m (Formula Text Syntax)
    psingles = do
      fs <- sepBy psingle (symbol "∧")
      case fs of 
        (_:_)  -> pure $ Conj fs
        _ -> fail "Can't have empty conjgation"

    psingle :: ParserT m (SingleConstraint Syntax)
    psingle = do
      core₁ <- syn_core level
      f <- (const (:≗:) <$> symbol "≗") <|> (const (:∈:) <$> symbol "⋵")
      core₂ <- syn_core level
      pure $ f core₁ core₂

