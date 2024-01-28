module Sigil.Abstract.Syntax
  ( Core(..)
  , Entry(..)
  , Module(..)
  , Package(..)
  , PackageHeader(..)
  , MTree(..)
  , ImportModifier(..)
  , ExportModifier(..)
  , ImportDef(..)
  , ExportDef(..)
  , Pattern(..)
  , Tel
  , Case
  , Forallχ
  , Coreχ
  , Varχ
  , Uniχ
  , Prdχ
  , Absχ
  , Appχ
  , Indχ
  , Ctrχ
  , Recχ
  , Eqlχ
  , ETCχ
  , CTEχ
  , Dapχ
  , TrLχ
  , TrRχ
  , LfLχ
  , LfRχ
  , Functorχ
  , Singleχ

  -- Lenses
  , package_header
  , package_modules
  , package_name
  , provides
  , requires
  
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
{- • Core    : The type of the core calculus.                                  -}
{- • Module  : The type of file-level modules.                                 -}
{- • Package : The type of packages, collections of modules.                   -}
{-                                                                             -}
{-------------------------------------------------------------------------------}


import Prelude hiding (lookup, length)

import Control.Lens (makeLenses, (^.))
import Data.Kind
import Data.List (intersperse)
import Data.List.NonEmpty (NonEmpty)
import qualified Data.List.NonEmpty as NonEmpty
import Data.Map (Map)
import Data.Set (Set)
import Data.Foldable
import Data.Bifunctor (bimap) 
import Data.Text hiding (zipWith, foldl', tail, head, intersperse, map)

import Prettyprinter

import Sigil.Abstract.Names

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
  deriving Eq

data Core b n χ
  = Coreχ (Coreχ b n χ)
  -- Atoms
  | Uniχ (Uniχ χ) Integer
  | Varχ (Varχ χ) n

  -- Products: Type definition, intro/elim
  | Prdχ (Prdχ χ) (b n (Core b n χ)) (Core b n χ)
  | Absχ (Absχ χ) (b n (Core b n χ)) (Core b n χ)
  | Appχ (Appχ χ) (Core b n χ) (Core b n χ)

  -- Generic Recursive Types: Type definition, intro/elim
  | Indχ (Indχ χ) n ((Functorχ χ) (Core b n χ)) [(Text, Core b n χ)]
  | Ctrχ (Ctrχ χ) Text ((Functorχ χ) (Core b n χ))
  | Recχ (Recχ χ) (b n (Core b n χ)) (Core b n χ) [Case b n χ]

  -- Structures: Type, intro, elim
  -- | Sigχ (Sigχ χ) [(Text, (b n (Core b n χ)))]
  -- | Sctχ (Sctχ χ) [(Text, (b n (Core b n χ)))]
  -- | Prjχ (Prjχ χ) (Core b n χ) Text

  -- All our Homotopy Types 
  -- Eql (ι) is an equality type
  -- ETC (↓) Extracts a 1-1-Correspondence from an equality
  -- CTE (↑) Constructs an equality from a 1-1-Correspondence 
  | Eqlχ (Eqlχ χ) (Tel b n (Core b n χ)) (Core b n χ) (Core b n χ) (Core b n χ)
  | ETCχ (ETCχ χ) (Core b n χ) 
  | CTEχ (CTEχ χ) (Core b n χ) 

  -- Dap (ρ) is a generalization of the reflexive equality constructor
  -- transport: given an ι (x ⮜ B a b ≜ p). A f g
  -- tr→ ⮜ A[x ↦ a] → A[x ↦ b]
  -- tr→   f[x ↦ a] ≜ g[x ↦ b] 
  -- tr← ⮜ A[x ↦ b] → A[x ↦ x]
  -- tr←   g[x ↦ b] ≜ f[x ↦ a] 
  -- further, lift→ ⮜ ι (x ≜ p). A f (tr→ (x ≜ p). A f)
  -- Sym transposes sqaures
  | Dapχ (Dapχ χ) (Tel b n (Core b n χ)) (Core b n χ)
  | TrRχ (TrRχ χ) (Tel b n (Core b n χ)) (Core b n χ) (Core b n χ)
  | TrLχ (TrLχ χ) (Tel b n (Core b n χ)) (Core b n χ) (Core b n χ) 
  | LfRχ (LfRχ χ) (Tel b n (Core b n χ)) (Core b n χ) (Core b n χ)
  | LfLχ (LfLχ χ) (Tel b n (Core b n χ)) (Core b n χ) (Core b n χ)
  -- | Symχ (Symχ χ) (Core b n χ) (Core b n χ)


type family Coreχ (b :: Type -> Type -> Type) n χ
type family Functorχ χ :: Type -> Type
type family Varχ χ
type family Uniχ χ
type family Prdχ χ
type family Absχ χ
type family Appχ χ
type family Indχ χ
type family Ctrχ χ
type family Recχ χ

type family Eqlχ χ
type family Dapχ χ
type family TrRχ χ
type family LfRχ χ
type family TrLχ χ
type family LfLχ χ
type family ETCχ χ
type family CTEχ χ
  

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

{--------------------------------- PACKAGE TYPE ----------------------------------}
{-                                                                                -}
{- •                                                                              -}
{---------------------------------------------------------------------------------}

data PackageHeader = PackageHeader
  { _package_name :: Text
  , _provides :: [Text]
  , _requires :: [Text]
  -- , _version :: (Int, Int, Int)
  -- , _options :: Options (optimization/debuggng etc.)
  }

data Package m = Package { _package_header :: PackageHeader
                         , _package_modules :: (MTree m)
                         }

newtype MTree a = MTree { untree :: Map Text (Maybe a, Maybe (MTree a)) }

$(makeLenses ''PackageHeader)
$(makeLenses ''Package)

instance Functor MTree where
  fmap f (MTree wmap) = MTree $ fmap (bimap (fmap f) (fmap (fmap f))) wmap

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
  = Module { _module_header :: Path
           , _module_imports :: [ImportDef]
           , _module_exports :: [ExportDef]
           , _module_entries :: [Entry b v χ]
           } 

data ImportModifier
  = ImWildcard
  | ImSingleton
  | ImAlias Text Text
  | ImExcept (Set Text)
  | ImGroup (Set Text)
  deriving (Ord, Eq, Show)

-- TODO Sealing
data ExportModifier
  = ExWildcard
  | ExAsType
  | ExSeal
  | ExSingleton
  deriving (Ord, Eq, Show)

newtype ImportDef = Im { unImport :: (NonEmpty Text, ImportModifier) }
  deriving (Eq, Ord, Show)

newtype ExportDef = Ex { unEexport :: (NonEmpty Text, ExportModifier) }
  deriving (Eq, Ord, Show)

-- TODO: add fields!
data Entry b n χ
  = Singleχ (Singleχ χ) (b n (Core b n χ)) (Core b n χ)

type family Singleχ χ

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

    Indχ _ name _ terms ->
      vsep [ "μ" <+> pretty_name name <+> "⮜" <+> "??fty" <+> "."
           , indent 2 (align (vsep $ map (\(text, ty) -> pretty text <+> pretty_core ty) terms))]
    Ctrχ _  label _ -> ":" <> pretty label
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

    -- Sigχ _ fields ->
    -- Sctχ _ fields ->
    -- Prjχ _ val field ->

    Eqlχ _ tel ty a a' ->
      ("ι"
       <+> pretty_tel tel
       <+> pretty_core ty
       <+> ("(" <> pretty_core a)
       <+> "="
       <+> (pretty_core a' <> ")"))
    ETCχ _ val -> pretty_core val <+> "↓"
    CTEχ _ val -> pretty_core val <+> "↑"

    Dapχ _ tel val ->
      ("ρ"
       <+> pretty_tel tel
       <+> pretty_core val)

    TrRχ _ tel ty val -> "⍄" <+> pretty_tel tel <+> pretty_core ty <+> pretty_core val
    TrLχ _ tel ty val -> "⍃" <+> pretty_tel tel <+> pretty_core ty <+> pretty_core val

    LfRχ _ tel ty val -> "⎕⍄" <+> pretty_tel tel <+> pretty_core ty <+> pretty_core val
    LfLχ _ tel ty val -> "⎕⍃" <+> pretty_tel tel <+> pretty_core ty <+> pretty_core val

  
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

pretty_entry_builder :: (b n (Core b n χ) -> Maybe n) -> (n -> Doc ann) -> (b n (Core b n χ) -> Doc ann) -> (Core b n χ -> Doc ann) -> Entry b n χ -> Doc ann
pretty_entry_builder name pretty_name pretty_bind pretty_core entry =
  case entry of
    (Singleχ _ bind val) ->
      vsep [ pretty_bind bind
           , maybe "_" pretty_name (name bind) <+> "≜" <+> align (pretty_core val) ]

pretty_mod_builder :: (Entry b n χ -> Doc ann) -> Module b n χ -> Doc ann
pretty_mod_builder pretty_entry m =
  -- TOOD: account for imports/exports
  vsep $
    ("module" <+> (foldl' (<>) "" . zipWith (<>) ("" : repeat ".") . fmap pretty . toList . unPath $ (m^.module_header)))
    : emptyDoc : intersperse emptyDoc (fmap (align . pretty_entry) (m^.module_entries))

pretty_path :: NonEmpty Text -> Doc ann  
pretty_path = fold . fmap pretty . NonEmpty.intersperse "."

instance Pretty ImportDef where
  pretty (Im (path, mod)) = pretty_path path <> case mod of
    ImWildcard -> ".(…)"
    ImSingleton -> ""
    ImAlias fm to -> "" <+> pretty fm <+> "→" <+> pretty to
    ImExcept set -> " \\" <+> (sep . fmap pretty . toList $ set)
    ImGroup set -> " (." <> (sep . fmap pretty . toList $ set) <> ")"
  
instance Pretty ExportDef where
  pretty (Ex (path, mod)) = pretty_path path <> case mod of
    ExWildcard -> ".(..)"
    ExAsType -> "astype??" -- TODO what did I mean??
    ExSeal -> "↓"
    ExSingleton -> ""

instance Pretty n => Pretty (Pattern n) where
  pretty pat =
    let pbracket p = case p of
          PatCtr _ _ -> "(" <> pretty p <> ")"
          PatVar _ -> pretty p
    in case pat of
      PatCtr n subpats -> pretty (":" <> n) <+> sep (map pbracket subpats)
      PatVar n -> pretty n
