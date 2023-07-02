{-# LANGUAGE ScopedTypeVariables #-}
{-# OPTIONS_GHC -Wno-unrecognised-pragmas #-}
module Glyph.Parse.Mixfix
  ( Precedences(..)
  , PrecedenceNode(..)
  , Operator(..)
  , Associativity(..)
  , Fixity(..)
  , PrecedenceGraph

  -- Lenses
  , fixity
  , name_parts

  , prec_ops
  , successors

  , prec_nodes
  , default_infix
  , default_prefix
  , default_postfix
  , default_closed
  , mixfix
  , update_precs
  ) where


{----------------------------- MIXFIX PARSER PHASE -----------------------------}
{- The mixfix parser works as follows:                                         -}      
{- • Users can create named precedence groups, e.g. 'generic-sum'              -}      
{- • Users can then specify precedence, e.g 'generic-sum' → 'generic-product'  -}      
{-   would indicate that operators in 'generic-product' are higher precedence  -}      
{-   (bind tighter) than those in 'generic-sum'                                -}      
{- • Users can insert any element into a precedence graph, e.g.                -}      
{-   • (infixr _⋅_ 'generic-product')                                          -}      
{-   • (prefix ±_ 'tight-prefix')                                              -}      
{-                                                                             -}      
{- Each category (infix(l/r/n), prefix, postfix) has a default precedence      -}      
{- group.                                                                      -}      
{- • Any closed expression is also a prefix operator with default precedence   -}      
{- • Any core expression in parentheses also counts as a closed operator with  -}      
{-   default precedence.                                                       -}      
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
import Prettyprinter
import Topograph

import Glyph.Concrete.Decorations.Range
import Glyph.Concrete.Parsed
import Glyph.Parse.Combinator
import Glyph.Parse.Lexer


{------------------------------ MIXFIX DATA TYPES ------------------------------}
{- The data-types follow as one would expect. Operators are either closed,     -}      
{- prefix, postfix or infix. Infix operators have an associativity (left,      -}      
{- right or non).                                                              -}      
{-                                                                             -}      
{- The PrecedenceNode and Precedences form a public interface used by other    -}      
{- bits of the parser. GraphNode and Telescope are used internally by the      -}      
{- parser. Telescope represents a telescopic application, while OperatorLike   -}      
{- allows 'operators' in the precedence graph to also be an injected closed    -}      
{- expression, or partially parsed expression.                                 -}      
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
  { _prec_nodes :: Map Text PrecedenceNode
  , _default_infix :: Text
  , _default_prefix :: Text
  , _default_postfix :: Text
  , _default_closed :: Text
  }

$(makeLenses ''Operator)
$(makeLenses ''PrecedenceNode)
$(makeLenses ''Precedences)


data Telescope a = Tel a [a]

data IsDefault = IsNone | IsClosed
  deriving (Eq, Ord)

type GraphNode = (IsDefault, Set Operator)

type PrecedenceGraph i = G GraphNode i

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
{- However, modifications have been made, as the grammars do not quite match.  -}      
{- highest precedence closed term is an expression in parentheses              -}      
{- just before that it is a prefix operation                                   -}      
{-                                                                             -}
{- + [1] : https://www.cse.chalmers.se/~nad/publications/                      -}
{-         danielsson-norell-mixfix.pdf                                        -}
{-                                                                             -}
{-                                                                             -}
{-                                                                             -}
{-------------------------------------------------------------------------------}      


mixfix :: Parser ParsedCore -> Parser ParsedCore -> Precedences -> Parser ParsedCore
mixfix atom core = run_precs (mixfix' atom core)

mixfix' :: forall i. Parser ParsedCore -> Parser ParsedCore -> PrecedenceGraph i -> Parser ParsedCore
mixfix' atom core (G {..}) = expr
  where
    expr :: Parser ParsedCore
    expr = foldl (App mempty) <$> precs gVertices <*> many (precs gVertices)
    
    precs :: [i] -> Parser ParsedCore
    precs (p:ps) = prec p <||> precs ps
    precs [] = customFailure "ran out of operators in precedence graph" 
  
    prec :: i -> Parser ParsedCore
    prec node = choice'
      [ unscope <$> close Closed
      , appn <$> psucs <*> close (Infix NonAssociative) <*> psucs
      , appr <$> many1 preRight <*> psucs
      , appl <$> psucs <*> many1 postLeft
      , customFailure "choice ran out of operators"
      ]

      where
        close :: Fixity -> Parser (Telescope ParsedCore)
        close f = inj f <||> (inner . ops current_ops) f
          where
            current_ops :: [Operator]
            current_ops = Set.toList $ view _2 $ gFromVertex node

            inj Closed =
              if view _1 (gFromVertex node) == IsClosed then
                flip Tel [] <$> (atom <||> between (symbol "(") (symbol ")") core)
              else
                fail "not default"
            inj _ = fail "not default"

        psucs :: Parser ParsedCore
        psucs = precs $ gEdges node

        preRight :: Parser (ParsedCore -> ParsedCore)
        preRight = 
              (\(Tel core lst) val -> unscope $ Tel core (lst <> [val])) <$> close Prefix
          <||> (\l (Tel core lst) r -> unscope $ Tel core (l : lst <> [r]))
               <$> psucs <*> close (Infix RightAssociative)

        postLeft :: Parser (ParsedCore -> ParsedCore)
        postLeft =
              (\(Tel core lst) val -> unscope $ Tel core (val : lst)) <$> close Postfix
          <||> (\(Tel core lst) l r -> unscope $ Tel core (r : lst <> [l]))
               <$> close (Infix LeftAssociative) <*> psucs

        appn e (Tel core lst) e' = unscope $ Tel core (e : lst <> [e'])
        appr fs e = foldr (\f e -> f e) e fs
        appl e fs = foldl (\e f -> f e) e fs

    inner :: [Operator] -> Parser (Telescope ParsedCore)
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
  

unscope :: Telescope ParsedCore -> ParsedCore
unscope (Tel core l) = go core l where
  go :: ParsedCore -> [ParsedCore] -> ParsedCore
  go core [] = core 
  go core (c:cs) = go (App (range core <> range c) core c) cs 
  


run_precs :: MonadFail m => (forall i. PrecedenceGraph i -> m a) -> Precedences -> m a
run_precs f precs = case construct_graph precs of
  Right graph -> case runG graph (f . closure) of
    Right m -> m
    Left _ -> fail "cycle in precedence graph"
  Left e -> fail $ show e

  where
    construct_graph :: Precedences -> Either Text (Map GraphNode (Set GraphNode))
    construct_graph precs = build (precs^.prec_nodes)
      where
        build = (\m -> foldl' (add_node m) (pure Map.empty) m) . to_graph_node

        to_graph_node :: Map Text PrecedenceNode -> Map Text (GraphNode, Set Text)
        to_graph_node = Map.mapWithKey (\k v -> ((isdefault k, v^.prec_ops), v^.successors))
          where 
            isdefault k
              | k == (precs^.default_closed) = IsClosed
              | otherwise = IsNone
        
        add_node :: Map Text (GraphNode, Set Text)
          -> Either Text (Map GraphNode (Set GraphNode))
          -> (GraphNode, Set Text)
          -> Either Text (Map GraphNode (Set GraphNode))
        add_node nodes m (ops, sucs) = do
          graph <- m
          sucs' <- mapM (\s -> case nodes^.at s of
                       Just pnode -> Right (pnode^._1)
                       Nothing -> Left ("can't find " <> s)) (Set.toList sucs)
          pure $ (at ops ?~ Set.fromList sucs') graph


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
    add_to_node name op = prec_nodes . at name %~ (Just . maybe (single op) (insert op))
      where 
        single op = PrecedenceNode (Set.singleton op) Set.empty
        insert op = prec_ops %~ Set.insert op


instance Pretty Operator where    
  pretty = pretty . opName

instance Pretty IsDefault where 
  pretty d = case d of 
    IsNone -> ""
    IsClosed -> "default-closed"

instance Pretty Precedences where 
  pretty precs = case run_precs (pure . pretty . lst . adjacencyList) precs of 
    Just p -> p
    Nothing -> "cycle in precedence graph"
    where
      lst = fmap (\(n, ns) -> ((_2 %~ Set.toList) n, fmap (_2 %~ Set.toList) ns))
