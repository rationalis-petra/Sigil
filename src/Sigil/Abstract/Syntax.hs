module Sigil.Abstract.Syntax
  ( Core(..)
  , Tel
  , Module(..)
  , Entry(..)
  , ImportModifier(..)
  , ExportModifier(..)
  , ImportDef
  , ExportDef
  , Pattern(..)
  , Case
  -- , Clause(..)
  , Forallχ
  , Coreχ
  , Varχ
  , Uniχ
  , Prdχ
  , Absχ
  , Appχ
  , Eqlχ
  , Dapχ
  , Indχ
  , Ctrχ
  , Recχ
  , Mutualχ
  , Singleχ

  -- lenses
  , module_header
  , module_imports
  , module_exports
  , module_entries

  -- Adapters/utility
  , pretty_core_builder
  , pretty_entry_builder
  , pretty_mod_builder
  ) where


{----------------------------------- SYNTAX ------------------------------------}
{- This file contains definitions relating to the syntax                       -}
{- • Core   : The type of the core calculus                                    -}
{- • Module : The type of file-level modules.                                  -}
{- • Clause : Type of Seuth clauses                                            -}
{-                                                                             -}
{-------------------------------------------------------------------------------}


import Prelude hiding (lookup, length)

import Control.Lens (makeLenses, (^.))
import Data.Kind
import Data.List (intersperse)
import Data.List.NonEmpty (NonEmpty)
import Data.Set (Set)
import Data.Foldable
import Data.Text hiding (zipWith, foldl', tail, head, intersperse, map)

import Prettyprinter

import Sigil.Abstract.Environment

{---------------------------------- CORE TYPE ----------------------------------}
{- The Core Type represents the calculus upon which Sigil. is based. It is      -}
{- the primary representation of terms used by the Compiler.                   -}
{-                                                                             -}
{- Core takes three type parameters, b, v and χ, which serve the following     -}
{- purposes:                                                                   -}
{- • b and v are linked: b represents the type of bindings, and v represents   -}
{-   variables. These are related, but may change independently - for example, -}
{-   we may have different bindings where types are optional vs required,      -}
{-   but variables remain unchanged                                            -}
{-   • Representing metavariables in unification                               -}
{-   • Representing names which have not yet been resolved after parsing       -}
{-   • Representing names amenable to α-equivalence (e.g. DeBruijn indices)    -}
{- • χ is used as part of the 'trees that grow' idiom, and is used to make     -}
{-   variants of the syntax tree. Variants can include extra nodes or attach   -}
{-   extra information to each node, e.g.                                      -}
{-   • Keeping track of the source file a value came from                      -}
{-   • Adding extra type information to a node                                 -}
{-   • Adding a new node for constants (numbers etc.)                          -}
{-------------------------------------------------------------------------------}

type Tel b n v = [(b n (v, v, v), v)]
type Case b n χ = (Pattern n, Core b n χ)

data Pattern n
  = PatCtr Text [Pattern n]
  | PatVar n

data Core b n χ
  = Coreχ (Coreχ b n χ)
  -- Atoms
  | Uniχ (Uniχ χ) Integer
  | Varχ (Varχ χ) n

  -- Products: Type definition, intro/elim
  | Prdχ (Prdχ χ) (b n (Core b n χ)) (Core b n χ)
  | Absχ (Absχ χ) (b n (Core b n χ)) (Core b n χ)
  | Appχ (Appχ χ) (Core b n χ) (Core b n χ)

  -- Heterogeneous Univalent identity type & Dependent Lifting of Identity Terms
  | Eqlχ (Eqlχ χ) (Tel b n (Core b n χ)) (Core b n χ) (Core b n χ) (Core b n χ)
  | Dapχ (Dapχ χ) (Tel b n (Core b n χ)) (Core b n χ)

  -- Generic Recursive Types: Type definition, intro/elim
  | Indχ (Indχ χ) (b n (Core b n χ)) [(Text, b n (Core b n χ))]
  | Ctrχ (Ctrχ χ) Text
  | Recχ (Recχ χ) (b n (Core b n χ)) (Core b n χ) [Case b n χ]

type family Coreχ (b :: Type -> Type -> Type) n χ
type family Varχ χ
type family Uniχ χ
type family Prdχ χ
type family Absχ χ
type family Appχ χ
type family Eqlχ χ
type family Dapχ χ
type family Indχ χ
type family Ctrχ χ
type family Recχ χ

type Forall (φ :: Type -> Constraint) b n χ
  = ( φ n
    , φ (b n (Core b n χ))
    , φ (b n (Core b n χ, Core b n χ, Core b n χ)) -- for equality!
    , φ (Coreχ b n χ)
    , φ (Uniχ χ)
    , φ (Varχ χ)
    , φ (Prdχ χ)
    , φ (Absχ χ)
    , φ (Appχ χ)
    , φ (Eqlχ χ)
    , φ (Dapχ χ)
    )

type Forallχ (φ :: Type -> Constraint) χ
  = ( φ (Uniχ χ)
    , φ (Varχ χ)
    , φ (Prdχ χ)
    , φ (Absχ χ)
    , φ (Appχ χ)
    , φ (Eqlχ χ)
    , φ (Dapχ χ)
    )


{---------------------------------- MODULE TYPE ----------------------------------}
{-                                                                               -}
{- ImortDef = Import definitions. These are divided into two parts:              -}
{- • The Prefix: A non-empty list of names, e.g. [data string] or [prelude]      -}
{- • The Postfix: Indicates what to do with the prefix:                          -}
{-   • Singleton: Tread the prefix as a path to any value, which is imported     -}
{-     e.g. ([data, string], singleton) will bring 'string' into scope.          -}
{-   • Wildcard: treat the prefix as a module path or inductive type; import all -}
{-     elements for example ([data, string], wildcard) will import all members   -}
{-     from the 'data.string' module into the current scope.                     -}
{-   • Except: given a set of strings, treat the path as indicating a module,    -}
{-     and import all fields except for the given set                            -}
{-   • Set: Given a set of strings, import                                       -}
{-                                                                               -}
{- • Postfix (for exports)                                                       -}
{-   • Singleton: Export the                                                     -}
{-   • Seal: Export the given value (assumed to be a type), but the definition   -}
{-     is not exposed for the purpose of judgemental equality.                   -}
{-   • As type: Export the given value, as a particular type (usually a subtype  -}
{-     of the given type).                                                       -}
{-                                                                               -}
{---------------------------------------------------------------------------------}


data Module b v χ  
  = Module { _module_header :: NonEmpty Text
           , _module_imports :: [ImportDef]
           , _module_exports :: [ExportDef]
           , _module_entries :: [Entry b v χ]
           } 

data ImportModifier
  = ImWildcard
  | ImSingleton
  | ImAlias Text
  | ImPortExcept (Set Text)
  | ImPortGroup (Set Text)
  deriving (Ord, Eq, Show)

-- TODO Sealing
data ExportModifier
  = ExWildcard
  | ExAsType
  | ExSeal
  | ExSingleton
  deriving (Ord, Eq, Show)

type ImportDef = (NonEmpty Text, ImportModifier)

type ExportDef = (NonEmpty Text, ExportModifier)

-- TODO: add fields!
data Entry b n χ
  = Singleχ (Singleχ χ) (b n (Core b n χ)) (Core b n χ)
  | Mutualχ (Mutualχ χ) [(n, Core b n χ, Core b n χ)]

type family Singleχ χ
type family Mutualχ χ 

$(makeLenses ''Module)

  
{--------------------------------- EQ INSTANCE ---------------------------------}
{- The Equal type class instance performs an equality check directly on the    -}
{- names - this means that an Eq instance is not α equality!                   -}
{- Use the Term typeclass for α-equality                                       -}
{-------------------------------------------------------------------------------}


instance (Forall Eq b n χ) => Eq (Entry b n χ) where
  v1 == v2 = case (v1, v2) of 
    (Singleχ _ name tipe, Singleχ _ name' tipe') ->
      name == name' && tipe == tipe'
    (Mutualχ _ lst, Mutualχ _ lst') ->
      and (zipWith (==) lst lst')
    _ -> False


instance (Forall Eq b n χ )
         => Eq (Core b n χ) where
  v1 == v2 = case (v1, v2) of 
    (Coreχ r, Coreχ r') ->
      r == r'
    (Uniχ χ n, Uniχ χ' n') ->
      χ == χ' && n == n'
    (Varχ χ n, Varχ χ' n') ->
      χ == χ' && n == n' 
    (Prdχ χ x t, Prdχ χ' x' t') ->
      χ == χ' && x == x' && t == t' 
    (Absχ χ x e, Absχ χ' x' e') ->
      χ == χ' && x == x' && e == e'  
    (Appχ χ l r, Appχ χ' l' r') ->
      χ == χ' && l == l' && r == r'
    (Eqlχ χ tel ty a1 a2, Eqlχ χ' tel' ty' a1' a2' ) ->
      χ == χ' && tel == tel' && ty == ty' && a1 == a1' && a2 == a2'
    (Dapχ χ tel val , Dapχ χ' tel' val') ->
      χ == χ' && tel == tel' && val == val'
    (_, _) -> False


{------------------------------ PRETTY PRINTING --------------------------------}
{-     Instances for printing syntax trees to via the Prettyprinter library    -}
{-------------------------------------------------------------------------------}

pretty_core_builder ::
  Binding b
  => (n -> Doc ann)
  -> (Coreχ b n χ -> Doc ann)
  -> Core b n χ
  -> Doc ann
pretty_core_builder pretty_name pretty_coreχ c =
  case c of
    Coreχ v -> pretty_coreχ v
    Uniχ _ n -> "𝕌" <> pretty_subscript n
      where
        pretty_subscript =
          pretty . fmap to_subscript . show
        to_subscript c = case c of 
          '0' -> '₀' 
          '1' -> '₁'
          '2' -> '₂'
          '3' -> '₃'
          '4' -> '₄'
          '5' -> '₅'
          '6' -> '₆'
          '7' -> '₇'
          '8' -> '₈'
          '9' -> '₉'
          _ -> c
  
    Varχ _ name -> pretty_name name
      
    Prdχ {} -> align $ sep $ head tel : zipWith (<+>) (repeat "→") (tail tel)
      where
        tel = telescope c
        
        telescope (Prdχ _ bind e) = pretty_ty_bind bind : telescope e
        telescope b = [pretty_core  b]
    
    Absχ _ bind e ->
      let (args, body) = telescope e
    
          telescope (Absχ _ bind e) =
            let (args, body) = telescope e in 
              (bind : args, body)
          telescope body = ([], body)
    
          pretty_args bind [] = pretty_fn_bind bind
          pretty_args v (x : xs) = pretty_args v [] <+> pretty_args x xs
      in
        ("λ " <> pretty_args bind args <> " →") <+> nest 2 (bracket body)

    -- telescoping
    Appχ χ l r -> sep $ bracket <$> unwind (Appχ χ l r)

    Eqlχ _ tel ty a a' ->
      ("ι"
       <+> pretty_tel tel
       <+> pretty_core ty
       <+> ("(" <> pretty_core a)
       <+> "="
       <+> (pretty_core a' <> ")"))

    Dapχ _ tel val ->
      ("ρ"
       <+> pretty_tel tel
       <+> pretty_core val)

  
    Indχ _ bind terms ->
      vsep [ "μ" <+> pretty_fn_bind bind <> "."
           , indent 2 (align (vsep $ map (\(text, bind) -> pretty text <> "/" <> pretty_fn_bind bind) terms))]
    Ctrχ _ label -> ":" <> pretty label
    Recχ _ recur val cases ->
      vsep ["φ" <+> pretty_fn_bind recur <> "," <+> pretty_core val <> "."
           , indent 2 (align (vsep $ map pretty_case cases)) ]
      where
        pretty_case (pat, body) = pretty_pat pat <+> "→" <+> pretty_core body
        pretty_pat = \case 
          PatCtr n subpats -> pretty (":" <> n) <+> sep (map pbracket subpats)
          PatVar n -> pretty_name n
        pbracket p = case p of
          PatCtr _ _ -> "(" <> pretty_pat p <> ")"
          PatVar _ -> pretty_pat p
    where 
        pretty_core = pretty_core_builder pretty_name pretty_coreχ

        pretty_tel tel =
          case map pretty_tentry tel of
            (hd:tl) -> align $ sep $ hd : zipWith (<+>) (repeat ",") tl
            [] -> "."

        pretty_tentry (b, v) = pretty_eql_bind b <+> "≜" <+> bracket v

        pretty_fn_bind b = case (name b, tipe b) of 
          (Just nm, Just ty) -> "(" <> pretty_name nm <+> "⮜" <+> pretty_core ty <> ")"
          (Just nm, Nothing) -> pretty_name nm
          (Nothing, Just ty) -> "(_" <+> "⮜" <+> pretty_core ty <> ")"
          (Nothing, Nothing) -> "_"
        pretty_ty_bind b = case (name b, tipe b) of 
          (Just nm, Just ty) -> "(" <> pretty_name nm <+> "⮜" <+> pretty_core ty <> ")"
          (Just nm, Nothing) -> "(" <> pretty_name nm <+> "⮜" <+> "_)"
          (Nothing, Just ty) -> pretty_core ty
          (Nothing, Nothing) -> "_"
        pretty_eql_bind b = case (name b, tipe b) of
          (Just nm, Just (ty, v1, v2)) -> pretty_name nm <+> "⮜" <+> pretty_core (Eqlχ (error "impossible") [] ty v1 v2)
          (Just nm, Nothing) -> pretty_name nm <+> "⮜" <+> "_"
          (Nothing, Just (ty, v1, v2)) -> "_" <+> "⮜" <+> pretty_core (Eqlχ (error "impossible") [] ty v1 v2)
          (Nothing, Nothing) -> "_"
  
        bracket v = if iscore v then pretty_core v else "(" <> pretty_core v <> ")"
        
        iscore (Uniχ _ _) = True
        iscore (Varχ _ _) = True
        iscore _ = False
      
        unwind (Appχ _ l r) = unwind l <> [r]
        unwind t = [t]


-- pretty_bind_builder :: 
--   (Core b n χ -> Doc ann)
--   -> (n -> Doc ann)
--   -> (Coreχ b n χ -> Doc ann)
--   -> Bool
--   -> b n (Core b n χ)
--   -> Doc ann
-- pretty_bind_builder pretty_core pretty_name pretty_core isFnc entry = 

pretty_entry_builder :: (b n (Core b n χ) -> Maybe n) -> (n -> Doc ann) -> (b n (Core b n χ) -> Doc ann) -> (Core b n χ -> Doc ann) -> Entry b n χ -> Doc ann
pretty_entry_builder name pretty_name pretty_bind pretty_core entry =
  case entry of
    (Singleχ _ bind val) ->
      vsep [ pretty_bind bind
           , maybe "_" pretty_name (name bind) <+> "≜" <+> align (pretty_core val) ]
    (Mutualχ _ entries) ->
      vsep $
        fmap pretty_decl entries <> fmap pretty_def entries
      where 
        pretty_decl (n, t, _) = pretty_name n <+> "⮜" <+> pretty_core t
        pretty_def (n, _, v) = pretty_name n <+> "≜" <+> pretty_core v


pretty_mod_builder :: (Entry b n χ -> Doc ann) -> Module b n χ -> Doc ann
pretty_mod_builder pretty_entry m =
  -- TOOD: account for imports/exports
  vsep $
    ("module" <+> (foldl' (<>) "" . zipWith (<>) ("" : repeat ".") . fmap pretty . toList $ (m^.module_header)))
    : emptyDoc : intersperse emptyDoc (fmap (align . pretty_entry) (m^.module_entries))
