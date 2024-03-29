{-# LANGUAGE ScopedTypeVariables #-}
{-# OPTIONS_GHC -Wno-unrecognised-pragmas #-}
module Sigil.Parse.Mixfix
  ( Precedences(..)
  , PrecedenceNode(..)
  , Operator(..)
  , Associativity(..)
  , Fixity(..)
  , PrecedenceGraph
  , MixT

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


import Prelude hiding (head, tail, last)

import Control.Lens
import Control.Monad (join)
import Data.Foldable (foldl')
import qualified Data.Vector as Vector
import Data.Vector (Vector, head, tail, last)
import qualified Data.Text as Text
import Data.Text (Text)
import qualified Data.Set as Set
import Data.Set (Set)
import qualified Data.Map as Map
import Data.Map (Map)

import Text.Megaparsec
import Prettyprinter hiding (lparen, rparen)
import Topograph

import Sigil.Concrete.Decorations.Implicit
import Sigil.Concrete.Decorations.Range
import Sigil.Concrete.Parsed
import Sigil.Parse.Syntax
import Sigil.Parse.Combinator


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

type MixT m = ParsecT Text [MixToken ParsedCore] m

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
{-------------------------------------------------------------------------------}      


mixfix :: Monad m => Precedences -> MixT m ParsedCore
mixfix = run_precs mixfix'

mixfix' :: forall i m. Monad m => PrecedenceGraph i -> MixT m ParsedCore
mixfix' (G {..}) = expr
  where
    expr :: MixT m ParsedCore
    expr = foldl (\l r-> App (range l <> range r) Regular l r) <$> precs gVertices <*> many (precs gVertices)
    
    precs :: [i] -> MixT m ParsedCore
    precs (p:ps) = prec p <||> precs ps
    precs [] = customFailure "ran out of operators in precedence graph" 
  
    prec :: i -> MixT m ParsedCore
    prec node = choice'
      [ unscope <$> close Closed
      , appn <$> psucs <*> close (Infix NonAssociative) <*> psucs
      , appr <$> many1 preRight <*> psucs
      , appl <$> psucs <*> many1 postLeft
      , customFailure "choice ran out of operators"
      ]

      where
        close :: Fixity -> MixT m (Telescope ParsedCore)
        close f = inj f <||> (inner . ops current_ops) f
          where
            current_ops :: [Operator]
            current_ops = Set.toList $ view _2 $ gFromVertex node

            inj Closed =
              if view _1 (gFromVertex node) == IsClosed then
                flip Tel [] <$> token (\case {Syn _ s -> Just s; _ -> Nothing}) Set.empty 
              else
                fail "not default"
            inj _ = fail "not default"

        psucs :: MixT m ParsedCore
        psucs = precs $ gEdges node

        preRight :: MixT m (ParsedCore -> ParsedCore)
        preRight = 
              (\(Tel core lst) val -> unscope $ Tel core (lst <> [val])) <$> close Prefix
          <||> (\l (Tel core lst) r -> unscope $ Tel core (l : lst <> [r]))
               <$> psucs <*> close (Infix RightAssociative)

        postLeft :: MixT m (ParsedCore -> ParsedCore)
        postLeft =
              (\(Tel core lst) val -> unscope $ Tel core (val : lst)) <$> close Postfix
          <||> (\(Tel core lst) l r -> unscope $ Tel core (r : lst <> [l]))
               <$> close (Infix LeftAssociative) <*> psucs

        appn e (Tel core lst) e' = unscope $ Tel core (e : lst <> [e'])
        appr fs e = foldr (\f e -> f e) e fs
        appl e fs = foldl (\e f -> f e) e fs

    inner :: [Operator] -> MixT m (Telescope ParsedCore)
    inner [] = customFailure "inner ran out of operators"
    inner (op : ops) = choice'  
      [ do r1 <- range <$> lookAhead (satisfy (const True)) 
           args <-
             betweenM
             (fmap (\n -> satisfy (\case {NamePart _ n' -> n == n'; _ -> False})) $ op^.name_parts) expr
           --r2 <- range <$> lookAhead (satisfy (const True))
           pure $ Tel (Var r1 (opName op)) args
      , inner ops ]

    -- Helper Functions: graph tools
    -- ops  : get all operators in a given node with a specified fixity
    --        also, get all operators of successor nodes
    ops :: [Operator] -> Fixity -> [Operator]
    ops op f = filter ((== f) . view fixity) op
  

betweenM :: Monad m => Vector (MixT m b) -> MixT m a -> MixT m [a]  
betweenM vec p = case length vec of 
  0 -> pure []
  1 -> head vec *> pure []
  2 -> between (head vec) (last vec) ((: []) <$> p)
  _ -> head vec *> ((:) <$> p <*> betweenM (tail vec) p)

  
unscope :: Telescope ParsedCore -> ParsedCore
unscope (Tel core l) = go core l where
  go :: ParsedCore -> [ParsedCore] -> ParsedCore
  go core [] = core 
  go core (c:cs) = go (App (range core <> range c) Regular core c) cs 


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
update_precs args g = foldl' add_op g ((join . map to_node) args) 
  where 
    to_node arg
      | is_empty arg   = []
      | is_infix arg   = [ Operator (Infix LeftAssociative) (to_parts arg)
                         , Operator Prefix  ((hide_post . to_parts) arg)
                         , Operator Postfix ((hide_pre . to_parts) arg)
                         , Operator Closed  ((hide_in. to_parts) arg) ]
      | is_prefix arg  = [ Operator Prefix (to_parts arg)
                         , Operator Closed ((hide_pre . to_parts) arg) ]
      | is_postfix arg = [ Operator Postfix (to_parts arg) 
                         , Operator Closed ((hide_post . to_parts) arg) ]
      | otherwise      = [ Operator Closed (to_parts arg) ]

    is_empty arg = arg == "_"

    is_infix arg = case (uncons arg, unsnoc arg) of 
      (Just ('_', _), Just (_, '_')) -> True
      _ -> False

    is_prefix arg = case unsnoc arg of   
      Just (_, '_') -> True
      _ -> False

    is_postfix arg = case uncons arg of    
      Just ('_', _) -> True
      _ -> False

    hide_post arg = case (uncons arg) of
      Just (part, rest) -> cons ("_" <> part) rest
      _ -> arg
    hide_pre arg = case (unsnoc arg) of
      Just (rest, part) -> snoc rest (part <> "_")
      _ -> arg
    hide_in = hide_pre . hide_post

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
