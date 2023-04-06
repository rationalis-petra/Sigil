{-# LANGUAGE ScopedTypeVariables #-}
module Glyph.Parse
  ( Range
  , Parsed
  , Precedences(..)
  , PrecedenceNode
  , PrecedenceGraph
  , Operator(..)
  , Associativity(..)
  , Fixity(..)
  , fixity
  , name_parts
  , mixfix
  , core
  , def
  , runParser ) where

{------------------------------------ PARSER -----------------------------------}
{- The Parsing algorithm contains two distinct parts: the 'primary grammar'    -}
{- and a mixfix subgrammar. These two parts are expressed in two different     -}
{- parsers.                                                                    -}
{-                                                                             -}
{-------------------------------------------------------------------------------}


import Prelude hiding (head, last, tail)
import Control.Lens
import Data.Foldable (foldl')
import qualified Data.Vector as Vector
import Data.Vector (Vector, head, last, tail)
import qualified Data.Text as Text
import Data.Text (Text, pack)
import qualified Data.Set as Set
import Data.Set (Set)
import qualified Data.Map as Map

import qualified Text.Megaparsec as Megaparsec
import Text.Megaparsec hiding (runParser)
import Text.Megaparsec.Char
import qualified Text.Megaparsec.Char.Lexer as L
import Topograph

import Glyph.Abstract.Syntax
import Glyph.Abstract.Environment (OptBind(..))
import Glyph.Concrete.Decorations.Range
import Glyph.Concrete.Parsed


{--------------------------------- PARSER TYPE ---------------------------------}


type Parser = Parsec Text Text


{------------------------------ MIXFIX DATA TYPES ------------------------------}
{- The parsing of mixifx operators is particularly finicky, and this           -} 
{- implementation is based on the paper Parsing Mixfix Operators [1].          -}
{-                                                                             -}
{- The basic idea is to represent all operators as either closed, prefix,      -}
{- postfix or infix. 'closed' operators have no leading or trailing            -}
{- underscores, ex. [_] or if_then_else_end. 'prefix' have a leading           -}
{- underscore, ex. _! or _a_|, 'postfix' have a trailing underscore,           -}
{- ex. if_then_else_ and -_. Finally, 'infix' have both, like _+_, and can be  -}
{- left, right or non associative.                                             -}
{-                                                                             -}
{- Precedence is denoted by a DAG, with nodes being sets of operators with     -}
{- equal precedence. Arrows point towards operators with higher precedence     -}
{- (i.e. operators which bind tighter).                                        -}
{-                                                                             -}      
{- The Telescope type is used to represent repeated left/right associative     -}      
{- applications.                                                               -}
{-                                                                             -}
{- + [1] : https://www.cse.chalmers.se/~nad/publications/                      -}
{-         danielsson-norell-mixfix.pdf                                        -}
{-                                                                             -}      
{-                                                                             -}      
{-------------------------------------------------------------------------------}      


data Associativity = LeftAssociative | RightAssociative | NonAssociative
  deriving (Eq, Ord, Show)
  
data Fixity = Closed | Prefix | Postfix | Infix Associativity 
  deriving (Eq, Ord, Show)

data Operator = Operator { _fixity :: Fixity, _name_parts :: Vector Text }
  deriving (Eq, Ord, Show)

type PrecedenceNode = (Set Operator)

type PrecedenceGraph i = G PrecedenceNode i

data Precedences = Precedences
  { _prec_fixed :: Map.Map PrecedenceNode (Set PrecedenceNode)
  , _prec_closed :: PrecedenceNode
  }

data Telescope χ = Tel (Core OptBind Text χ) [Core OptBind Text χ]

$(makeLenses ''Operator)
$(makeLenses ''Precedences)

  
{--------------------------------- CORE PARSER ---------------------------------}
{- The core parser first looks for the head of an expression (λ, let, etc.)    -}
{- before handing it off to the mixfix parser.                                 -}
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
{- before handing it off to the mixfix parser.                                 -}
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
    pexpr = run_precs precs mixfix

run_precs :: Precedences -> (forall i. PrecedenceGraph i -> Parser a) -> Parser a
run_precs precs f =
  let 
    graph = Map.insert (precs^.prec_closed) Set.empty $
      fmap (Set.insert (precs^.prec_closed)) (precs^.prec_fixed)

  in case runG graph (f . closure) of
    Right m -> m
    Left _ -> fail "cycle in precedence graph"

update_precs :: [Text] -> Precedences -> Precedences
update_precs args g = foldl' add_prec g (map to_node args) 
  where 
    to_node arg
  -- TODO: currently, '_' is treated as infix!!
      | is_infix arg   = Left $ Operator (Infix LeftAssociative) (to_parts arg)
      | is_prefix arg  = Left $ Operator Prefix (to_parts arg)
      | is_postfix arg = Left $ Operator Postfix (to_parts arg)
      | otherwise      = Right $ Operator Closed (to_parts arg)

    is_infix arg = case (uncons arg, unsnoc arg) of 
      (Just ('_', _), Just (_, '_')) -> True
      _ -> False

    is_prefix arg = case unsnoc arg of   
      Just (_, '_') -> True
      _ -> False

    is_postfix arg = case uncons arg of    
      Just ('_', _) -> True
      _ -> False

    to_parts :: Text -> Vector Text
    to_parts = Vector.fromList . filter (not . Text.null) . Text.splitOn "_" 

    add_prec precs prec = case prec of
      Left fix -> (prec_fixed %~ Map.insert (Set.singleton fix) Set.empty) precs
      Right close -> (prec_closed %~ Set.insert close) precs
  
 
{----------------------------- MIXFIX PARSER PHASE -----------------------------}
{-                                                                             -}
{- this operator denotes parallel choice, and is defined in the 'helper        -}
{- function' section, below the main mixfix parser                             -}
infixl 3 <||>
{-                                                                             -}
{- There is currently a bug in the parser: with the below graph, the & and  =  -}
{- operators do not parse correctly, e.g. true = false parses as true.         -}
{- However, the + and - operators do parse correctly. This seems to be related -}
{- to their position in the graph as changing associativity to right/non does  -}
{- not affect the outcome - the bug remains.                                   -}
{-                                                                             -}
{- (_&_ right) -> (_=_ non) -> (_+_ left) -> (_!) -> (if_then_else_) -> (_)    -}
{-                             (_-_ left)                                      -}
{- -> (false) -> (true)                                                        -}
{-------------------------------------------------------------------------------}      


mixfix :: forall i. PrecedenceGraph i -> Parser RawCore
mixfix G {..} = expr
  where
    expr :: Parser (RawCore)
    expr = precs gVertices
    
    precs :: [i] -> Parser (RawCore)
    precs (p:ps) = prec p <||> precs ps
    precs [] = customFailure "ran out of operators in precedence graph" 
  
    prec :: i -> Parser (RawCore)
    prec node = choice'
      [ unscope <$> close Closed
      , appn <$> psucs <*> close (Infix NonAssociative) <*> psucs
      , appr <$> many1 preRight <*> psucs
      , appl <$> psucs <*> many1 postLeft
      , customFailure "choice ran out of operators"
      ]

      where
        close :: Fixity -> Parser (Telescope Parsed)
        close = inner . ops current_ops
          where
            current_ops :: [Operator]
            current_ops = Set.toList $ gFromVertex node

        psucs :: Parser (RawCore)
        psucs = precs $ gEdges node

        preRight :: Parser (RawCore -> RawCore)
        preRight = 
              (\(Tel core lst) val -> unscope $ Tel core (lst <> [val])) <$> close Prefix
          <||> (\l (Tel core lst) r -> unscope $ Tel core (l : lst <> [r]))
               <$> psucs <*> close (Infix RightAssociative)

        postLeft :: Parser (RawCore -> RawCore)
        postLeft =
              (\(Tel core lst) val -> unscope $ Tel core (val : lst)) <$> close Postfix
          <||> (\(Tel core lst) l r -> unscope $ Tel core (r : lst <> [l]))
               <$> close (Infix LeftAssociative) <*> psucs

        appn e (Tel core lst) e' = unscope $ Tel core (e : lst <> [e'])
        appr fs e = foldr (\f e -> f e) e fs
        appl e fs = foldl (\e f -> f e) e fs

    inner :: [Operator] -> Parser (Telescope Parsed)
    inner [] = customFailure "inner ran out of operators"
    inner (op : ops) = choice'  
      [ do start <- getSourcePos
           args <- betweenM (fmap symbol $ op^.name_parts) expr
           end <- getSourcePos
           pure $ Tel (Var (Range $ Just (start, end)) (opName op)) args
      , inner ops ]

    -- Helper Functions: graph tools
    -- ops  : get all operators in a given node with a specified fixity
    --        also, get all operators of successor nodes
    ops :: [Operator] -> Fixity -> [Operator]
    ops op f = filter ((== f) . view fixity) op
  

unscope :: Telescope Parsed -> RawCore
unscope (Tel core l) = go core l where
  go :: RawCore -> [RawCore] -> RawCore
  go core [] = core 
  go core (c:cs) = go (App (range core <> range c) core c) cs 

(<||>) :: Parser a -> Parser a -> Parser a
l <||> r = try l <|> try r
  
choice' :: [Parser a] -> Parser a
choice' = choice . fmap try

opName :: Operator -> Text
opName (Operator {..}) = case _fixity of
  Closed -> name
  Prefix -> name <> "_" 
  Postfix -> "_"<> name 
  Infix _ -> "_" <> name <> "_"
  where name = underscore (Vector.toList _name_parts)
        underscore [] = ""
        underscore [x] = x
        underscore (x:y:[]) = x <> "_" <> y
        underscore (x:y:xs) = x <> "_" <> y <> "_" <> underscore xs

betweenM :: Vector (Parser b) -> Parser a -> Parser [a]  
betweenM vec p = case length vec of 
  0 -> pure []
  1 -> head vec *> pure []
  2 -> between (head vec) (last vec) ((\x -> [x]) <$> p)
  _ -> (head vec) *> ((:) <$> p <*> betweenM (tail vec) p)

many1 :: Parser a -> Parser [a]
many1 p = (:) <$> p <*> many p 


{-------------------------------- LEXING TOOLS ---------------------------------}


sc :: Parser () 
sc = L.space
  space1
  (L.skipLineComment ";;")
  (L.skipBlockComment "(;;" ";;)")

symbol :: Text -> Parser Text
symbol = L.symbol sc

lexeme :: Parser a -> Parser a
lexeme = L.lexeme sc

anyvar :: Parser Text  
anyvar = lexeme $ pack <$> (many1 (satisfy symchar))
  where 
    symchar :: Char -> Bool
    symchar '('  = False
    symchar ')'  = False
    symchar '['  = False
    symchar ']'  = False
    symchar '≜'  = False
    symchar ' '  = False
    symchar '\n' = False
    symchar '\r' = False
    symchar '\t' = False
    symchar _    = True


{------------------------------ RUNNING A PARSER -------------------------------}


runParser :: Parser a -> Text -> Text -> Either Text a
runParser p file input = case Megaparsec.runParser p (Text.unpack file) input of
  Left err -> Left $ Text.pack $ show $ err
  Right val -> Right val
