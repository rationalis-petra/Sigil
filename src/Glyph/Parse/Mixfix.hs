{-# LANGUAGE ScopedTypeVariables #-}
module Glyph.Parse.Mixfix
  ( Precedences(..)
  , PrecedenceNode(..)
  , PrecedenceGraph
  , Operator(..)
  , Associativity(..)
  , Fixity(..)
  , fixity
  , name_parts
  , mixfix
  , run_precs
  , update_precs

  -- Lenses
  , successors
  , 
  ) where


{----------------------------- MIXFIX PARSER PHASE -----------------------------}
{- The mixfix parser works as follows:                                         -}      
{- • Users can create named precedence groups, e.g. 'generic-sum'              -}      
{- • Users can then specify precedence, e.g 'generic-sum' → 'generic product   -}      
{- • Users can insert any element into a precedence graph, e.g.                -}      
{-   • (infixr _⋅_ 'generic-product')                                          -}      
{-   • (prefix ±_ 'tight-prefix')                                              -}      
{-                                                                             -}      
{- Each category (infix(l/r/n), prefix, postfix) has a default precedence      -}      
{- group.                                                                      -}      
{-                                                                             -}      
{-------------------------------------------------------------------------------}      


import Control.Lens
import Data.Foldable (foldl')
import qualified Data.Vector as Vector
import Data.Vector (Vector)
import qualified Data.Text as Text
import Data.Text (Text)
import qualified Data.Set as Set
import Data.Set (Set)
import qualified Data.Map as Map
import Data.Map (Map)

import Text.Megaparsec
import Topograph

import Glyph.Abstract.Syntax
import Glyph.Abstract.Environment
import Glyph.Concrete.Decorations.Range
import Glyph.Concrete.Parsed
import Glyph.Parse.Combinator
import Glyph.Parse.Lexer


{------------------------------ MIXFIX DATA TYPES ------------------------------}
{-                                                                             -}      
{-                                                                             -}      
{-------------------------------------------------------------------------------}      


data Associativity = LeftAssociative | RightAssociative | NonAssociative
  deriving (Eq, Ord, Show)
  
data Fixity = Closed | Prefix | Postfix | Infix Associativity 
  deriving (Eq, Ord, Show)

data Operator = Operator
  { _fixity :: Fixity
  , _name_parts :: Vector Text
  }
  deriving (Eq, Ord, Show)

data PrecedenceNode = PrecedenceNode
  { _prec_ops :: Set Operator
  , _successors :: Set Text
  }

data Precedences = Precedences
  { _prec_nodes :: Map.Map Text PrecedenceNode
  , _default_infix :: Text
  , _default_prefix :: Text
  , _default_postfix :: Text
  , _default_closed :: Text
  }

data Telescope χ = Tel (Core OptBind Text χ) [Core OptBind Text χ]

$(makeLenses ''Operator)
$(makeLenses ''PrecedenceNode)
$(makeLenses ''Precedences)


{----------------------------- MIXFIX PARSER PHASE -----------------------------}
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
{- However, Modifications:                                                     -}      
{- lowest priority closed term is an expression in parentheses                 -}      
{- just before that it is a prefix operation                                   -}      
{-                                                                             -}
{- + [1] : https://www.cse.chalmers.se/~nad/publications/                      -}
{-         danielsson-norell-mixfix.pdf                                        -}
{-                                                                             -}
{-                                                                             -}
{-                                                                             -}
{-------------------------------------------------------------------------------}      

type PrecedenceGraph i = G (Set Operator) i

mixfix :: forall i. Parser RawCore -> PrecedenceGraph i -> Parser RawCore
mixfix core (G {..}) = expr
  where
    expr :: Parser RawCore
    expr = precs gVertices

    paren_core = between (symbol "(") (symbol ")") core
    
    precs :: [i] -> Parser RawCore
    precs (p:ps) = prec p <||> precs ps
    precs [] = -- paren_core
      customFailure "ran out of operators in precedence graph" 
  
    prec :: i -> Parser RawCore
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

        psucs :: Parser RawCore
        psucs = precs $ gEdges node

        preRight :: Parser (RawCore -> RawCore)
        preRight = 
              (\(Tel core lst) val -> unscope $ Tel core (lst <> [val])) <$> (close Prefix <||> close Closed <||> (flip Tel [] <$> paren_core))
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

{----------------------------- GRAPH MANIPULATION ------------------------------}
{-- Exported utilities: manipulate a precedence graph                         --}
{-------------------------------------------------------------------------------}
  
run_precs :: Precedences -> (forall i. PrecedenceGraph i -> Parser a) -> Parser a
run_precs precs f = case construct_graph (precs^.prec_nodes) of
  Right graph -> case runG graph (f . closure) of
    Right m -> m
    Left _ -> fail "cycle in precedence graph"
  Left e -> fail $ show e

  where
    construct_graph :: Map Text PrecedenceNode -> Either Text (Map (Set Operator) (Set (Set Operator)))
    construct_graph nodes = foldl' add_node (pure Map.empty) nodes
      where
        add_node :: Either Text (Map (Set Operator) (Set (Set Operator))) -> PrecedenceNode -> Either Text (Map (Set Operator) (Set (Set Operator)))
        add_node m (PrecedenceNode {_prec_ops=p, _successors=sucs}) = do
          graph <- m
          sucs' <- mapM (\s -> case nodes^.at s of
                       Just pnode -> Right (pnode^.prec_ops)
                       Nothing -> Left ("can't find " <> s)) (Set.toList sucs)
          pure $ (at p ?~ (Set.fromList sucs')) graph


update_precs :: [Text] -> Precedences -> Precedences
update_precs args g = foldl' add_op g (map to_node args) 
  where 
    to_node arg
  -- TODO: currently, '_' is treated as infix!!
      | is_infix arg   = Operator (Infix LeftAssociative) (to_parts arg)
      | is_prefix arg  = Operator Prefix (to_parts arg)
      | is_postfix arg = Operator Postfix (to_parts arg)
      | otherwise      = Operator Closed (to_parts arg)

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

    add_op precs op = case op of
      (Operator (Infix _) _) -> add_to_node (precs^.default_infix)   op precs
      (Operator Prefix    _) -> add_to_node (precs^.default_prefix)  op precs
      (Operator Postfix   _) -> add_to_node (precs^.default_postfix) op precs
      (Operator Closed    _) -> add_to_node (precs^.default_closed)  op precs
  
    add_to_node :: Text -> Operator -> Precedences -> Precedences
    add_to_node name op = prec_nodes.(at name) %~ (Just . maybe (single op) (insert op))
      where 
        single op = PrecedenceNode (Set.singleton op) Set.empty
        insert op = prec_ops %~ Set.insert op

    
