module Spec.Sigil.Parse (parse_spec) where

import Prelude hiding (abs, pi, mod)
import Control.Monad.Reader (runReader)
import Data.Functor.Classes
import Data.List.NonEmpty (NonEmpty (..))
import Data.Text (Text, unpack)
import qualified Data.Map as Map
import Data.Map (Map)
import qualified Data.Set as Set
import qualified Data.Vector as Vec

import Text.Megaparsec
import Prettyprinter
import Prettyprinter.Render.Sigil

import TestFramework
import Sigil.Parse ()
import Sigil.Parse.Syntax
import Sigil.Parse.Outer
import Sigil.Parse.Mixfix
import Sigil.Abstract.Names (Path(..))
import Sigil.Abstract.Syntax
import Sigil.Abstract.AlphaEq
import Sigil.Concrete.Parsed
  

expr_ops :: Map Text PrecedenceNode
expr_ops = Map.fromList
  [ ("ctrl",  PrecedenceNode node_ctrl  (Set.fromList ["ppd"]))
  , ("eq",    PrecedenceNode node_eq    (Set.fromList ["sum"]))
  , ("sum",   PrecedenceNode node_sum   (Set.fromList ["prod"]))
  , ("prod",  PrecedenceNode node_prod  (Set.fromList ["ppd"]))
  , ("ppd",   PrecedenceNode node_ppd   (Set.fromList ["tight"]))
  , ("tight", PrecedenceNode node_tight (Set.fromList ["close"]))
  , ("close", PrecedenceNode node_close (Set.empty))
  ]

  where 
    node_eq    = Set.fromList [eq_op, neq_op]
    node_sum   = Set.fromList [add_op, sub_op, or_op]
    node_prod  = Set.fromList [times_op, dot_op, and_op]
    node_ppd   = Set.fromList [fact_op, f_op, g_op]
    node_tight = Set.fromList [pm_op]
    node_ctrl  = Set.fromList [if_op]
    node_close = Set.fromList [true, false]
    
    if_op    = Operator Prefix $ Vec.fromList ["if", "then", "else"]
    eq_op    = Operator (Infix NonAssociative)   $ Vec.fromList ["="]
    neq_op   = Operator (Infix NonAssociative)   $ Vec.fromList ["≠"]

    or_op    = Operator (Infix RightAssociative) $ Vec.fromList ["∨"]
    add_op   = Operator (Infix LeftAssociative)  $ Vec.fromList ["+"]
    sub_op   = Operator (Infix LeftAssociative)  $ Vec.fromList ["-"]

    and_op   = Operator (Infix RightAssociative) $ Vec.fromList ["∧"]
    dot_op   = Operator (Infix LeftAssociative)  $ Vec.fromList ["⋅"]
    times_op = Operator (Infix LeftAssociative)  $ Vec.fromList ["×"]

    fact_op  = Operator Postfix $ Vec.fromList ["!"]
    f_op     = Operator Prefix $ Vec.fromList ["f"]
    g_op     = Operator Prefix $ Vec.fromList ["g"]

    pm_op    = Operator Prefix $ Vec.fromList ["±"]
   
    true     = Operator Closed $ Vec.singleton "true"
    false    = Operator Closed $ Vec.singleton "false"


precs :: Precedences
precs = Precedences
  { _prec_nodes=expr_ops
  , _default_infix   = "sum"
  , _default_prefix  = "ppd"
  , _default_postfix = "ppd"
  , _default_closed  = "close"
  }

parse_spec :: TestGroup
parse_spec = TestGroup "parsing" $ Left
  [ parse_lit
  , parse_mixfix precs
  , parse_expr 
  , parse_entry 
  , parse_mod
  ]
      
-- parsing of mixfix operations 
parse_mixfix :: Precedences -> TestGroup
parse_mixfix precs = TestGroup "mixfix" $ Right
    -- Simple tests
    [ mixfix_test "lit-true" [np "true"] (var "true")
    , mixfix_test "lit-false" [np "false"] (var "false")
    , mixfix_test "lit-false" [np "false"] (var "false")
    --, mixfix_test "simple-closed" "( true )" (var "(_)" ⋅ var "true")
    , mixfix_test "simple-postfix" [np "true", np "!"] (var "_!" ⋅ var "true" )
    , mixfix_test "simple-prefix" [np "f", np "true"] (var "f_" ⋅ var "true")
    , mixfix_test "simple-non-assoc" [np "true", np "=", np "false"] (var "_=_" ⋅ var "true" ⋅ var "false")
    , mixfix_test "simple-left-assoc" [np "true", np "+", np "false"] (var "_+_" ⋅ var "true"  ⋅ var "false")
    , mixfix_test "simple-right-assoc" [np "true", np "∧", np "false"] (var "_∧_" ⋅ var "true"  ⋅ var "false")
    , mixfix_test "close_app" [np "true", np "true"] (var "true" ⋅ var "true")

    , mixfix_test "simple-close-prefix" [np "true", np "true"] (var "true" ⋅ var "true")
    , mixfix_test "multi-prefix" [np "f", np "true", np "true"] (var "f_" ⋅ var "true" ⋅ var "true")

    -- Multiple name parts tests
    , mixfix_test "simple-multiname-prefix" [np "if", np "true", np "then", np "false" , np"else", np "true"]
           (var "if_then_else_" ⋅ var "true" ⋅ var "false" ⋅ var "true")
    -- , mixfix_test "simple-multiname-postfix"
    -- , mixfix_test "simple-multiname-nonassoc"
    -- , mixfix_test "simple-multiname-left-assoc"
    -- , mixfix_test "simple-multiname-right-assoc" 

    -- Associativity Tests
    , mixfix_test "multiple-right-assoc" [np "true", np "∧", np "false", np "∧", np "false"]
      (var "_∧_"
       ⋅ var "true"
       ⋅ (var "_∧_" ⋅ var "false" ⋅ var "false"))

    , mixfix_test "multiple-left-assoc" [np "true", np "+", np "false", np "-", np "false"]
      (var "_-_"
        ⋅ (var "_+_" ⋅ var "true"  ⋅ var "false")
        ⋅ var "false")

    , mixfix_test "binop-precedence" [np "true", np "+", np "false", np "⋅", np "false"]
      (var "_+_" ⋅ var "true"  ⋅ (var "_⋅_" ⋅ var "false" ⋅ var "false"))
    ]

  where
    mixfix_test :: Text -> [MixToken ParsedCore] -> ParsedCore -> Test
    mixfix_test name input out =  
      case runParser (mixfix precs) (unpack name) input of  
        Right val ->
          if αeq val out then
            Test name Nothing
          else
            Test name $ Just $
              vsep ["got:" <+> annotate (fg_colour (dull white)) (pretty val)
                   , "expected:" <+> annotate (fg_colour (dull white)) (pretty out) ]
        Left _ -> Test name $ Just "parse err"

parse_lit :: TestGroup
parse_lit =
  TestGroup "literal" $ Right
    [ lit_test "universe-0"   "𝕌"   (mix [sy (𝓊 0)])
    , lit_test "universe-0v2" "𝕌₀"  (mix [sy (𝓊 0)])
    , lit_test "universe-1"   "𝕌₁"  (mix [sy (𝓊 1)])
    , lit_test "universe-10"  "𝕌₁₀" (mix [sy (𝓊 10)])
    , lit_test "universe-23"  "𝕌₂₃" (mix [sy (𝓊 23)])
    ]

  where
    lit_test :: Text -> Text -> Syntax -> Test
    lit_test name text out =  
      case runReader (runParserT (syn_core pos1) (unpack name) text) pos1 of  
        Right val ->
          if syn_eq val out then
            Test name Nothing
          else
            Test name $ Just $ vsep [ "got:" <+> "(" <> pretty val <>")"
                                    , "expected:" <+> "(" <> pretty out <> ")"]
        Left msg -> Test name $ Just $ pretty $ errorBundlePretty msg

parse_expr :: TestGroup
parse_expr =
  TestGroup "expression" $ Right
    [ expr_test "universe-in-expr" "𝕌 + 𝕌" (mix [sy (𝓊 0), np "+", sy (𝓊 0)])
    , expr_test "univar-lamb" "λ x → true" (abs ["x"] (mix [np "true"]))
    , expr_test "bivar-lamb" "λ x y → false" (abs ["x", "y"] (mix [np "false"]))

    , expr_test "closed-lamb"
      "λ x → x"
      (abs ["x"] (mix [np "x"]))
    , expr_test "closed-lamb-newline"
      "λ x → x\n"
      (abs ["x"] (mix [np "x"]))
    , expr_test "infix-lamb"
      "λ _x_ → true x true"
      (abs ["_x_"] (mix [np "true", np "x", np "true"]))
    , expr_test "infix-closed-lamb"
      "λ _x_ th fo → th x fo"
      (abs ["_x_", "th", "fo"] (mix [np "th", np "x", np "fo"]))
    , expr_test "prefix-lamb-1"
      "λ x_ → x true"
      (abs ["x_"] (mix [np "x", np "true"]))
    , expr_test "prefix-lamb-2"
      "λ x → x true"
      (abs ["x"] (mix [np "x", np "true"]))
    , expr_test "postfix-lamb"
      "λ _x → true x"
      (abs ["_x"] (mix [np "true", np "x"]))

    , expr_test "uni-uni-app"
      "𝕌 𝕌"
      (mix [sy (𝓊 0), sy (𝓊 0)])
    -- slow
    , expr_test "lamb-in-expr"
      "(λ x_ → x true) + ( λ x_ → x true )"
      (mix [sy (abs ["x_"] (mix [np "x", np "true"])), np "+", sy (abs ["x_"] (mix [np "x", np "true"]))])
    , expr_test "uni-uni-paren-app"
      "(𝕌 𝕌)"
      (mix [sy (mix [sy (𝓊 0), sy (𝓊 0)])])
    , expr_test "lam-var-app"
      "(λ x_ → x true) true"
      (mix [sy (abs ["x_"] (mix [np "x", np "true"])),  np "true"])
    , expr_test "lam-uni-app"
      "(λ x_ → x true) 𝕌"
      (mix [sy (abs ["x_"] (mix [np "x", np "true"])), sy (𝓊 0)])
    , expr_test "lam-lam-app"
      "(λ x → x true) (λ x → x true)"
      (mix [sy (abs ["x"] (mix [np "x", np "true"])), sy (abs ["x"] (mix [np "x", np "true"]))])
    , expr_test "lam-parens-app"
      "(λ x → x true) 𝕌"
      (mix [sy (abs ["x"] (mix [np "x", np "true"])), sy (𝓊 0)])
    -- With Mixfix
    , expr_test "lam-binop" -- TODO: remove annotation
      "λ (A ⮜ 𝕌) → A + A"
      (lam [("A", mix [sy (𝓊 0)])] (mix [np "A", np "+", np "A"]))
    , expr_test "lam-parens"
      "λ (A ⮜ 𝕌) → (A + A)"
      (lam [("A", mix [sy (𝓊 0)])] (mix [sy (mix [np "A", np "+", np "A"])]))
    , expr_test "lam-parens-2"
      "λ (A ⮜ 𝕌) → A (A A)"
      (lam [("A", mix [sy (𝓊 0)])] (mix [np "A", sy (mix [np "A", np "A"])]))
    , expr_test "lam-parens-2"
      "λ (A ⮜ 𝕌) → A (A A) A"
      (lam [("A", mix [sy (𝓊 0)])] (mix [np "A", sy (mix [np "A", np "A"]), np "A"]))

    , expr_test "lam-parens-3"
      "λ m n → m n ( m n ) m"
      (abs ["m", "n"] (mix [np "m", np "n", sy (mix [np "m", np "n"]), np "m"]))


    -- Lambda: Annotations, multiple arguments etc.
    , expr_test "lam-ann"
      "λ (A ⮜ 𝕌) → A"
      (lam [("A", mix [sy (𝓊 0)])] (mix [np "A"]))
    , expr_test "lam-many"
      "λ (A ⮜ 𝕌) (B ⮜ 𝕌) → A"
      (lam [("A", mix [sy (𝓊 0)]), ("B", mix [sy (𝓊 0)])] (mix [np "A"]))
    , expr_test "lam-dep"
      "λ (A ⮜ 𝕌) (x ⮜ A) → x"
      (lam [("A", mix [sy (𝓊 0)]), ("x", mix [np "A"])] (mix [np "x"]))

    -- Product: Annotations, multiple arguments etc.
    , expr_test "prd-ann"
      "(A ⮜ 𝕌) → A"
      (pi [("A", mix [sy (𝓊 0)])] (mix [np "A"]))
    , expr_test "prd-noann"
      "𝕌 → 𝕌"
      ([mix [sy (𝓊 0)]] → mix [sy (𝓊 0)])

    -- Inductive Types: 
    , expr_test "ind-empty"
    "μ N ⮜ 𝕌." (μ "N" (mix [sy (𝓊 0)]) [])

    , expr_test "ind-nat"
    "μ N ⮜ 𝕌.\n  zero ⮜ N\n  succ ⮜ N → N"
     (μ "N" (mix [sy (𝓊 0)])
      [ ("zero", mix [np "N"])
      , ("succ", [mix [np "N"]] → mix [np "N"])])

    , expr_test "ind-nat-extra-line"
    "μ N ⮜ 𝕌.\n  zero ⮜ N\n  succ ⮜ N → N\n  "
     (μ "N" (mix [sy (𝓊 0)])
      [ ("zero", mix [np "N"])
      , ("succ", [mix [np "N"]] → mix [np "N"])])


    -- Recursive definitions
    , expr_test "rec-nat"
    "φ rec ⮜ N → N, m.\n  :zero → n\n  :succ n → succ (rec i)"
    (φ (Just "rec") (Just ([mix [np "N"]] → mix [np "N"])) (mix [np "m"])
     [ (pl "zero", mix [np "n"])
     , (pc "succ" [pv "n"], mix [np "succ", sy (mix [np "rec", np "i"])])])

    , expr_test "rec-nat-extra-line"
    "φ rec ⮜ N → N, m.\n  :zero → n\n  :succ n → succ (rec i)\n"
    (φ (Just "rec") (Just ([mix [np "N"]] → mix [np "N"])) (mix [np "m"])
     [ (pl "zero", mix [np "n"])
     , (pc "succ" [pv "n"], mix [np "succ", sy (mix [np "rec", np "i"])])])
    ]
  where
    expr_test :: Text -> Text -> Syntax -> Test
    expr_test name text out =  
      case runReader (runParserT (syn_core pos1) (unpack name) text) pos1 of  
        Right val ->
          if syn_eq val out then
            Test name Nothing
          else
            Test name $ Just $ vsep ["got:" <+> "(" <> pretty val <>")", "expected:" <+> "(" <> pretty out <> ")"]
        Left msg -> Test name $ Just $ pretty $ errorBundlePretty msg


parse_entry :: TestGroup
parse_entry = 
  TestGroup "definition" $ Right
    [ entry_test "literal"
      "x ≜ true"
      (sentry "x" (mix [np "true"]))
    , entry_test "recursive"
      "x ≜ x"
      (sentry "x" (mix [np "x"]))
    , entry_test "parameter"
      "id y ≜ y"
      (sentry "id" (abs ["y"] (mix [np "y"])))
    , entry_test "infix-param"
      "twice _*_ y ≜ y * y"
      (sentry "twice" (abs ["_*_", "y"] (mix [np "y", np "*", np "y"])))
    , entry_test "posfix-param"
      "post-app x _~ ≜ x ~"
      (sentry "post-app" (abs ["x", "_~"] (mix [np "x", np "~"])))
    ]
  where
    entry_test :: Text -> Text -> SynEntry -> Test
    entry_test name text out =  
      case runReader (runParserT syn_entry (unpack name) text) pos1 of  
        Right val ->
          if syn_ent_eq val out then
            Test name Nothing
          else
            Test name $ Just $ vsep ["got:" <+> pretty val, "expected:" <+> pretty out]
        Left msg -> Test name $ Just $ pretty $ errorBundlePretty msg

parse_mod :: TestGroup
parse_mod = 
  TestGroup "module" $ Right
    [ mod_test "empty"
      "module empty"
      (smodul (Path ["empty"]) [] [] [])

    , mod_test "importer"
      "module importer\n import\n  var"
      (smodul (Path ["importer"]) [Im (Path ("var" :| []), ImSingleton)] [] []) 

    , mod_test "single-def"
      "module single-def \n\
      \x ≜ true"
      (smodul (Path ["single-def"]) [] []
       [sentry "x" (mix [np "true"])])

    , mod_test "multi-def"
      "module multi-def \n\
      \x ≜ true\n\
      \y ≜ false"
      (smodul (Path ["multi-def"]) [] []
       [ sentry "x" (mix [np "true"])
       , sentry "y" (mix [np "false"])])

    , mod_test "complex-modul"
      "module complex-modul \n\
      \fn ≜ λ (A ⮜ 𝕌₁) (x ⮜ A) → A\n\
      \val ≜ fn 𝕌"
      (smodul (Path ["complex-modul"]) [] []
       [ sentry "fn" (lam [("A", mix [sy (𝓊 1)]), ("x", mix [np "A"])] (mix [np "A"]))
       , sentry "val" (mix [np "fn", sy (𝓊 0)])
       ])
    ]
  where
    mod_test :: Text -> Text -> SynModule -> Test
    mod_test name text out =  
      case runReader (runParserT syn_mod (unpack name) text) pos1 of  
        Right val ->
          if syn_mod_eq val out then
            Test name Nothing
          else
            Test name $ Just $ vsep ["got:", pretty val, "expected:", pretty out]
        Left msg -> Test name $ Just $ pretty $ errorBundlePretty msg

𝓊 :: Integer -> Syntax  
𝓊 = RUni mempty

abs :: [Text] -> Syntax -> Syntax
abs = flip $ foldr (\var body -> RAbs mempty (Just var) Nothing body)

lam :: [(Text, Syntax)] -> Syntax -> Syntax
lam = flip $ foldr (\(v, s) body -> RAbs mempty (Just v) (Just s) body)

pi :: [(Text, Syntax)] -> Syntax -> Syntax
pi = flip $ foldr (\(v, s) body -> RPrd mempty (Just v) (Just s) body)

(→) :: [Syntax] -> Syntax -> Syntax
(→) = flip $ foldr (\ty body -> RPrd mempty Nothing (Just ty) body)

μ :: Text -> Syntax -> [(Text, Syntax)] -> Syntax
μ var ty = RInd mempty var (Just ty)

φ :: Maybe Text -> Maybe Syntax -> Syntax -> [(Pattern Text, Syntax)] -> Syntax
φ = RRec mempty

mix :: [MixToken Syntax] -> Syntax
mix = RMix mempty

sentry :: Text -> Syntax -> SynEntry
sentry name val = RSingle mempty name (Nothing) val

smodul :: Path -> [ImportDef] -> [ExportDef] -> [SynEntry] -> SynModule
smodul = RModule

np :: Text -> MixToken s
np = NamePart

sy :: s -> MixToken s
sy = Syn

pc :: Text -> [Pattern Text] -> Pattern Text
pc = PatCtr

pl :: Text -> Pattern Text
pl v = PatCtr v []

pv :: Text -> Pattern Text
pv = PatVar

-- Parsed Core
-- 𝓊c :: Integer -> ParsedCore  
-- 𝓊c = Uniχ mempty
  
(⋅) :: ParsedCore -> ParsedCore -> ParsedCore
(⋅) = Appχ mempty

var :: Text -> ParsedCore  
var = Varχ mempty



-- equality
syn_eq :: Syntax -> Syntax -> Bool
syn_eq l r = case (l, r) of 
  (RMix _ toks, RMix _ toks') ->
    liftEq (tok_eq syn_eq) toks toks'
  (RUni _ n, RUni _ n') ->
    n == n'
  (RPrd _ mt mty body, RPrd _ mt' mty' body') ->
    liftEq (==) mt mt'
    && liftEq syn_eq mty mty'
    && syn_eq body body'
  (RAbs _ mt mty body, RAbs _ mt' mty' body') ->
    liftEq (==) mt mt'
    && liftEq syn_eq mty mty'
    && syn_eq body body'
  (REql _ tel ty v1 v2, REql _ tel' ty' v1' v2') ->
    tel_eq tel tel' && syn_eq ty ty' && syn_eq v1 v1' && syn_eq v2 v2'
  (RDap _ tel prf, RDap _ tel' prf') ->
    tel_eq tel tel' && syn_eq prf prf'
  (RInd _ name mty ctors    , RInd _ name' mty' ctors') ->
    name == name' && liftEq syn_eq mty mty' && liftEq ctor_eq ctors ctors'
    where 
      ctor_eq (label, ty) (label', ty') = label == label' && syn_eq ty ty'
  (RCtr _ name mty, RCtr _ name' mty') ->
    name == name' && liftEq syn_eq mty mty'
  (RRec _ mtx mty val cases , RRec _ mtx' mty' val' cases') ->
    liftEq (==) mtx mtx'
    && liftEq syn_eq mty mty'
    && syn_eq val val'
    && liftEq case_eq cases cases'
    where 
      case_eq (pat, syn) (pat', syn') = pat == pat' && syn_eq syn syn'
  _ -> False
  where
    tel_eq l r = liftEq tel_part_eq l r
    tel_part_eq (mt, ms, v) (mt', ms', v') = 
      liftEq (==) mt mt'
      && liftEq (\(a, b, c) (a', b', c') -> syn_eq a a' && syn_eq b b' && syn_eq c c') ms ms'
      && syn_eq v v'

  -- [(Maybe Text, Maybe (Syntax, Syntax, Syntax), Syntax)]

tok_eq :: (Syntax -> Syntax -> Bool) -> MixToken Syntax -> MixToken Syntax -> Bool
tok_eq f l r = case (l, r) of  
  (NamePart p, NamePart p') -> p == p'
  (Syn s, Syn s')           -> f s s'
  _                         -> False

syn_ent_eq :: SynEntry -> SynEntry -> Bool
syn_ent_eq (RSingle _ nm mty val) (RSingle _ nm' mty' val') =
  nm == nm' && liftEq syn_eq mty mty' && syn_eq val val'

syn_mod_eq :: SynModule -> SynModule -> Bool
syn_mod_eq (RModule header imports exports entries) (RModule header' imports' exports' entries') = 
  header == header' && imports == imports' && exports == exports' && liftEq syn_ent_eq entries entries'
