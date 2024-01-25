{-# OPTIONS_GHC -Wno-orphans #-}
module Sigil.Parse
  ( Range
  , Parsed
  , core
  , entry
  , mod
  , formula
  ) where


{------------------------------------ PARSER -----------------------------------}
{- The Parsing algorithm contains two distinct parts: the 'core grammar'       -}
{- and a mixfix subgrammar. These two parts are expressed in two different     -}
{- parsers.                                                                    -}
{-                                                                             -}
{- This file contains the 'pore grammar', which describes how to parse         -}
{- modules and various built-int constructs like functions, pattern matching   -}
{- etc. Function application is handed off to the mixfix subgrammar, which     -}
{- can only pase 'core' terms if they are enclosed in parentheses.             -}
{-------------------------------------------------------------------------------}


import Prelude hiding (head, last, tail, mod)
import Control.Monad.Except (MonadError, throwError)
import qualified Data.Text as Text
import Data.Text (Text)
import Data.Maybe (maybeToList)
import Data.Foldable (fold)

import qualified Text.Megaparsec as Megaparsec
import Text.Megaparsec hiding (runParser, parse)
import Prettyprinter.Render.Sigil (SigilDoc)
import Prettyprinter hiding (lparen, rparen)

import Sigil.Abstract.Syntax
import Sigil.Abstract.Unify
import Sigil.Abstract.Names (Path(..), OptBind(..), name)
import Sigil.Concrete.Decorations.Range
import Sigil.Concrete.Parsed

import Sigil.Parse.Lexer (scn)
import Sigil.Parse.Syntax
import Sigil.Parse.Combinator
import Sigil.Parse.Outer
import Sigil.Parse.Mixfix


mod :: MonadError SigilDoc m => Text -> ([ImportDef] -> m Precedences)
  -> Text -> Text -> m ParsedModule
mod package_name get_precs filename input = do
  raw_mod <- parse syn_mod filename input
  mix_mod package_name get_precs raw_mod

entry :: MonadError SigilDoc m => Precedences -> Text -> Text -> m ParsedEntry
entry precs filename input = do
  raw_entry <- parse syn_entry filename input
  mix_entry precs raw_entry

core :: MonadError SigilDoc m => Precedences -> Text -> Text -> m ParsedCore
core precs filename input = do
  raw_core <- parse (scn *> syn_core pos1 <* scn <* eof) filename input
  mix_core precs raw_core

formula :: MonadError SigilDoc m => Precedences -> Text -> Text -> m (Formula Text ParsedCore)
formula precs filename input = do
  raw_core <- parse (scn *> syn_formula pos1 <* scn <* eof) filename input
  mix_formula precs raw_core
 

update_precs_def :: Precedences -> ParsedEntry -> Precedences
update_precs_def precs def =
  case def of 
    Singleχ _ bind _ -> update_precs (maybeToList . name $ bind) precs

  
{-------------------------------- MODULE PARSER --------------------------------}
{- The module parser parses                                                    -}
{-                                                                             -}
{-------------------------------------------------------------------------------}      

mix_mod :: MonadError SigilDoc m => Text -> ([ImportDef] -> m Precedences) -> SynModule -> m ParsedModule
mix_mod package_name get_precs (RModule title imports exports entries) = do
  precs <- get_precs imports
  body <- let go precs = \case
                [] -> pure []
                (entry : entries) -> do
                  entry' <- mix_entry precs entry
                  (:) entry' <$> go (update_precs_def precs entry') entries
          in go precs entries
  pure $ Module (Path (package_name, title)) imports exports body


mix_entry :: forall m. MonadError SigilDoc m => Precedences -> SynEntry -> m ParsedEntry
mix_entry precs = \case
  RSingle range nm ms val ->
    Singleχ range <$> (OptBind . (Just nm,) <$> mapM (mix_core precs) ms) <*> mix_core precs val

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


mix_core :: forall m. MonadError SigilDoc m => Precedences -> Syntax -> m ParsedCore
mix_core precs = \case
  RMix _ vals -> do
    let go [] = pure []
        go (c:cs) = case c of 
          Syn v -> (:) <$> (Syn <$> mix_core precs v) <*> go cs 
          NamePart r p -> (NamePart r p :) <$> go cs
    vals' <- go vals
    parseMix (mixfix precs) vals'
  RUni rn n -> pure $ Uniχ rn n 
  RPrd rn aty mt ms body ->
    Prdχ (rn, aty)
    <$> (OptBind . (mt ,) <$> mapM (mix_core precs) ms)
    <*> mix_core (update_precs (maybeToList mt) precs) body
  RAbs rn aty mt ms body ->
    Absχ (rn, aty)
    <$> (OptBind . (mt ,) <$> mapM (mix_core precs) ms)
    <*> mix_core (update_precs (maybeToList mt) precs) body
  RInd rn nm mty ctors ->
    let precs' = update_precs [nm] precs
        mix_ctors = mapM mix_ctor
        mix_ctor (txt, ty) = (txt, ) <$> mix_core precs' ty
    in Indχ rn nm <$> (mapM (mix_core precs) mty) <*> mix_ctors ctors 
  RCtr rn nm mty -> Ctrχ rn nm <$> mapM (mix_core precs) mty

  RRec rn mt mty val cases ->
    let mix_case (pat, body) = (pat, ) <$> mix_core (update_precs (pat_vars pat) precs') body
        pat_vars = \case 
          PatVar n -> [n]
          PatCtr _ subpats -> fold (map pat_vars subpats)
        precs' = update_precs (maybeToList mt) precs
    in Recχ rn 
    <$> (OptBind . (mt,) <$> mapM (mix_core precs) mty)
    <*> mix_core precs val
    <*> mapM mix_case cases

  REql rn rt ty v1 v2 -> do
    (tel', precs') <- mix_tel precs rt []
    Eqlχ rn tel' <$> mix_core precs' ty <*> mix_core precs' v1 <*> mix_core precs' v2
  RETC rn val -> ETCχ rn <$> mix_core precs val
  RCTE rn val -> CTEχ rn <$> mix_core precs val

  RDap rn tel ref -> do
    (tel', precs') <- mix_tel precs tel []
    Dapχ rn tel' <$> mix_core precs' ref
  RTrL rn tel ty val -> do
    (tel', precs') <- mix_tel precs tel []
    TrLχ rn tel' <$> mix_core precs' ty <*> mix_core precs' val
  RTrR rn tel ty val -> do
    (tel', precs') <- mix_tel precs tel []
    TrRχ rn tel' <$> mix_core precs' ty <*> mix_core precs' val
  RLfL rn tel ty val -> do
    (tel', precs') <- mix_tel precs tel []
    LfLχ rn tel' <$> mix_core precs' ty <*> mix_core precs' val
  RLfR rn tel ty val -> do
    (tel', precs') <- mix_tel precs tel []
    LfRχ rn tel' <$> mix_core precs' ty <*> mix_core precs' val

  where
    mix_tel :: Precedences
      -> [(Maybe Text, Maybe (Syntax, Syntax, Syntax), Syntax)]
      -> [(OptBind Text (ParsedCore, ParsedCore, ParsedCore), ParsedCore)]
      -> m ([(OptBind Text (ParsedCore, ParsedCore, ParsedCore), ParsedCore)]
         , Precedences)
    mix_tel precs [] out = pure (reverse out, precs)
    mix_tel precs ((mt, mid, pf) : ps) out = do
          mid' <- mapM (\(ty, a, a') -> (,,)
                         <$> mix_core precs ty
                         <*> mix_core precs a
                         <*> mix_core precs a') mid
          pf' <- mix_core precs pf
          mix_tel (update_precs (maybeToList mt) precs) ps ((OptBind (mt, mid'), pf') : out) 

mix_scons :: forall m. MonadError SigilDoc m => Precedences -> SingleConstraint Syntax -> m (SingleConstraint ParsedCore)
mix_scons precs = \case
  (l :≗: r) -> (:≗:) <$> mix_core precs l <*> mix_core precs r
  (l :∈: r) -> (:∈:) <$> mix_core precs l <*> mix_core precs r

mix_formula :: forall m. MonadError SigilDoc m => Precedences -> Formula Text Syntax -> m (Formula Text ParsedCore)
mix_formula precs = \case
  Conj cons -> Conj <$> mapM (mix_scons precs) cons
  And l r -> And <$> mix_formula precs l <*> mix_formula precs r
  Bind q n ty f -> Bind q n <$> mix_core precs ty <*> mix_formula (update_precs [n] precs) f

{------------------------------ RUNNING A PARSER -------------------------------}


parseMix :: MonadError SigilDoc m => MixT m a -> [MixToken ParsedCore] -> m a
parseMix p input = do
  result <- Megaparsec.runParserT p "mixfix" input
  case result of 
    Left _ -> throwError $ "precedence error in:" <+> pretty input
    -- Left (ParseErrorBundle errs _) ->
    --   throwError $ sep $ map pretty_err (toList errs)
    --     where pretty_err = \case
    --             TrivialError _ mactual expected -> "got" <+> pretty (show mactual) <> ", expected" <+> pretty (show expected)
    --             FancyError _ errs ->
    --               "[" <> sep (map (pretty . show) . toList $ errs) <> "]"  
    Right val -> pure val

parse :: MonadError SigilDoc m => ParserT m a -> Text -> Text -> m a
parse p file input = do
  result <- Megaparsec.runParserT p (Text.unpack file) input
  case result of 
    Left err -> throwError $ pretty $ errorBundlePretty err
    Right val -> pure val

instance ShowErrorComponent Text where 
  showErrorComponent = Text.unpack

-- instance VisualStream [MixToken ParsedCore] where
--   showTokens _ toks = show $ vsep $ map pretty (toList toks)

-- instance TraversableStream [MixToken ParsedCore] where
--   reachOffsetNoLine o state = 
