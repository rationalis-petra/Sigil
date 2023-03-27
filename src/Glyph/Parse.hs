{-# LANGUAGE ScopedTypeVariables #-}
module Glyph.Parse (Range,
              Parsed,
              PrecedenceNode,
              PrecedenceGraph,
              Operator(..),
              Associativity(..),
              Fixity(..),
              fixity,
              name_parts,
              mixfix,
              core,
              runParser) where


{------------------------------------ PARSER -----------------------------------}
{- The Parsing algorithm contains two distinct parts: the 'primary grammar'    -}
{- and a mixfix subgrammar. These two parts are expressed in two different     -}
{- parsers.                                                                    -}
{-                                                                             -}
{-                                                                             -}
{-                                                                             -}
{-                                                                             -}
{-------------------------------------------------------------------------------}


import Prelude hiding (head, last, tail)
import Control.Lens
import qualified Data.Vector as Vector
import Data.Vector (Vector, head, last, tail)
import qualified Data.Text as Text
import Data.Text (Text, pack)
import qualified Data.Set as Set
import Data.Set (Set)
import Data.Void (Void)

import qualified Text.Megaparsec as Megaparsec
import Text.Megaparsec hiding (runParser)
import Text.Megaparsec.Char
import qualified Text.Megaparsec.Char.Lexer as L
import Topograph

import Glyph.Abstract.Syntax
import Glyph.Abstract.Environment (OptBind(..))


type Parser = Parsec Text Text

type RawCore = Core OptBind Text Parsed

type Range = ([Text], Int, Int)
  
empty_range :: Range
empty_range = ([], -1, -1)

join_ranges :: Range -> Range -> Range
join_ranges (t, s, e) (_, s', e') = (t, min s s', max e e')

data Parsed
type instance Coreχ Parsed = Void
type instance Varχ Parsed = Range
type instance Uniχ Parsed = Range
type instance Prdχ Parsed = Range
type instance Absχ Parsed = Range
type instance Appχ Parsed = Range

range :: Core b n Parsed -> Range
range (Coreχ _) = empty_range
range (Uni r _) = r
range (Var r _) = r
range (Prd r _ _) = r
range (Abs r _ _) = r
range (App r _ _) = r


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
{-------------------------------------------------------------------------------}      


data Associativity = LeftAssociative | RightAssociative | NonAssociative
  deriving (Eq, Ord, Show)
  
data Fixity = Closed | Prefix | Postfix | Infix Associativity 
  deriving (Eq, Ord, Show)

data Operator = Operator { _fixity :: Fixity, _name_parts :: Vector Text }
  deriving (Eq, Ord, Show)

type PrecedenceNode = (Set Operator)

type PrecedenceGraph i = G PrecedenceNode i

data Telescope χ = Tel (Core OptBind Text χ) [Core OptBind Text χ]

$(makeLenses ''Operator)


{--------------------------------- CORE PARSER ---------------------------------}
{- The core parser first looks for the head of an expression (λ, let, etc.)    -}
{- before handing it off to the mixfix parser.                                 -}
{-                                                                             -}
{-------------------------------------------------------------------------------}      


core :: PrecedenceGraph i -> Parser RawCore
core graph = choice [plam, pexpr]
  where
    plam :: Parser RawCore
    plam = do
      let unscope :: [Text] -> RawCore -> RawCore
          unscope = flip $ foldr (\v rest -> Abs empty_range (OptBind $ Left v) rest)

          args :: Parser [Text]
          args = between (symbol "[") (symbol "]") (many1 arg)  

          arg :: Parser Text
          arg = anyvar

      _ <- symbol "λ"
      tel <- args

      -- Currently, symbols introduced in a lambda are not added to the
      -- parse-graph, so λ [_+_] (2 + 3) wouldn't work
      body <- core graph
      pure $ unscope tel body

    pexpr :: Parser (RawCore)
    pexpr = (mixfix graph)

 
{----------------------------- MIXFIX PARSER PHASE -----------------------------}

-- this operator denotes parallel choice, and is defined in the 'helper
-- function' section, below the main mixfix parser
infixl 3 <||>

{- There is currently a bug in the parser: with the below graph, the & and  =  -}
{- operators do not parse correctly, e.g. true = fales parses as true.         -}
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
    -- 'Toplevel' parsers that are returned by the function
    -- TOOD: top_prec → like prec, but ensures that must parse eof
    expr :: Parser (RawCore)
    expr = precs gVertices
    
    precs :: [i] -> Parser (RawCore)
    precs (p:ps) = prec p <||> precs ps
    precs [] = customFailure "ran out of operators in precedence graph" 
  
    prec :: i -> Parser (RawCore)
    prec node = choice
      [ try (unscope <$> close Closed)
      , try (appn <$> psucs <*> close (Infix NonAssociative) <*> psucs)
      , try (appr <$> (many1 preRight) <*> psucs)
      , try (appl <$> psucs <*> (many1 postLeft))
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
    inner (op : ops) =
      Tel (Var empty_range (opName $ op))
        <$> betweenM (fmap symbol $ _name_parts op) expr
      <||> inner ops

    -- Helper Functions: graph tools
    -- ops  : get all operators in a given node with a specified fixity
    --        also, get all operators of successor nodes
    -- sucs : get all successors (adjacent nodes with higher precedence)
    ops :: [Operator] -> Fixity -> [Operator]
    ops op f = filter ((== f) . _fixity) op
  

unscope :: Telescope Parsed -> RawCore
unscope (Tel core l) = go core l where
  go :: RawCore -> [RawCore] -> RawCore
  go core [] = core 
  go core (c:cs) = go (App (join_ranges (range core) (range c)) core c) cs 

(<||>) :: Parser a -> Parser a -> Parser a
l <||> r = try l <|> r   

opName :: Operator -> Text
opName (Operator {..}) = case _fixity of
  Closed -> name
  Prefix -> "_" <> name
  Postfix -> name <> "_"
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
    symchar ' '  = False
    symchar '\n' = False
    symchar '\r' = False
    symchar '\t' = False
    symchar _    = True

symbol :: Text -> Parser Text
symbol = L.symbol sc


{------------------------------ RUNNING A PARSER -------------------------------}


runParser :: Parser a -> Text -> Text -> Either Text a
runParser p file input = case Megaparsec.runParser p (Text.unpack file) input of
  Left err -> Left $ Text.pack $ show $ err
  Right val -> Right val



  
