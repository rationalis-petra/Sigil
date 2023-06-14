module Glyph.Abstract.Syntax
  ( Core(..)
  , Module(..)
  , Definition(..)
  , ImportDef(..)
  , IndType(..)
  -- , Clause(..)
  , Forallχ
  , Coreχ
  , Varχ
  , Uniχ
  , Prdχ
  , Absχ
  , Appχ
  , Mutualχ
  , SigDefχ
  , IndDefχ

  -- Adapters/utility
  , pretty_core_builder
  , pretty_def_builder
  ) where


{----------------------------------- SYNTAX ------------------------------------}
{- This file contains definitions relating to the syntax                       -}
{- • Core   : The type of the core calculus                                    -}
{- • Module : The type of file-level modules.                                  -}
{- • Clause : Type of Seuth clauses                                            -}
{-                                                                             -}
{-------------------------------------------------------------------------------}


import Prelude hiding (lookup, length)

import Data.Kind
import Data.Foldable
import Data.Text hiding (zipWith, foldl', tail, head)

import Prettyprinter


{---------------------------------- CORE TYPE ----------------------------------}
{- The Core Type represents the calculus upon which Glyph is based. It is      -}
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


data Core b n χ
  = Coreχ (Coreχ b n χ)
  -- The Core Calculus, based on Martin Löf
  | Uniχ (Uniχ χ) Int 
  | Varχ (Varχ χ) n
  | Prdχ (Prdχ χ) (b n (Core b n χ)) (Core b n χ)
  | Absχ (Absχ χ) (b n (Core b n χ)) (Core b n χ)
  | Appχ (Appχ χ) (Core b n χ) (Core b n χ)

  -- Type Families - with name and uid
  -- | Fam Text Integer [Core n χ]

  -- Inductive + Coinductive constants - now with name!
  -- | Ive n [Core n χ] --
  -- | Cve [Core n χ]   --
  -- | Match [Pattern]  --
  -- | CoCall           --

  -- Records constants - with name and uid
  -- | Sct [(b (Core b v χ), Core b v χ)]
  -- | Sig [(b (Core b v χ), Core b v χ)]
  -- | Dot


-- Type Families

type family Coreχ (b :: Type -> Type -> Type) n χ
type family Varχ χ
type family Uniχ χ
type family Prdχ χ
type family Absχ χ
type family Appχ χ

type Forall (φ :: Type -> Constraint) b n χ
  = ( φ n
    , φ (b n (Core b n χ))
    , φ (Coreχ b n χ)
    , φ (Uniχ χ)
    , φ (Varχ χ)
    , φ (Prdχ χ)
    , φ (Absχ χ)
    , φ (Appχ χ)
    )

type Forallχ (φ :: Type -> Constraint) χ
  = ( φ (Uniχ χ)
    , φ (Varχ χ)
    , φ (Prdχ χ)
    , φ (Absχ χ)
    , φ (Appχ χ)
    )


{---------------------------------- MODULE TYPE ----------------------------------}
{-                                                                               -}
{-                                                                               -}
{-                                                                               -}
{---------------------------------------------------------------------------------}


data Module b v χ  
  = Module { _module_name :: [Text]
           , _module_exports :: [Text]
           , _module_imports :: [ImportDef]
           , _module_defs :: [(b v (Core b v χ), Definition b v χ)]
           } 

data ImportDef
  = ImportOne [Text] Text
  | ImportAll [Text] Text
  | ImportSet [Text] [Text]
  | ImportExcept [Text] [Text]

data IndType = Inductive | Coinductive  
  deriving (Eq, Ord, Show)

data Definition b n χ
  = Mutualχ (Mutualχ χ) [(b n (Core b n χ), Core b n χ)]
  | SigDefχ (SigDefχ χ) IndType (b n (Core b n χ)) [(b n (Core b n χ))]
  | IndDefχ (IndDefχ χ) IndType (b n (Core b n χ)) [(b n (Core b n χ))]
  -- | SctDef (b n (Core b n χ)) [(b n (Core b n χ))]

type family Mutualχ χ 
type family SigDefχ χ
type family IndDefχ χ 

{--------------------------------- EQ INSTANCE ---------------------------------}
{- The Equal type class instance performs an equality check directly on the    -}
{- names - this means that an Eq instance is not α equality!                   -}
{- Use the Term typeclass for α-equality                                       -}
{-------------------------------------------------------------------------------}


instance (Forall Eq b n χ) --Eq (b n (Core b n χ)), Eq n, Forallχ Eq χ, Eq (Coreχ b n χ))
          => Eq (Definition b n χ) where
  v1 == v2 = case (v1, v2) of 
    (Mutualχ _ defs, Mutualχ _ defs') -> defs == defs'
    (SigDefχ _ itype bind fields, SigDefχ _  itype' bind' fields') ->
      itype == itype' && bind == bind' && fields == fields'
    (IndDefχ _ itype bind terms, IndDefχ _ itype' bind' terms') ->
      itype == itype' && bind == bind' && terms == terms'
    (_, _) -> False

instance Forall Eq b n χ --(Eq (b n (Core b n χ)), Eq n, Forallχ Eq χ, Eq (Coreχ b n χ))
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
    (_, _) -> False


{------------------------------ PRETTY PRINTING --------------------------------}
{-     Instances for printing syntax trees to via the Prettyprinter library    -}
{-------------------------------------------------------------------------------}

pretty_def_builder :: (b n (Core b n χ) -> Doc ann) -> (n -> Doc ann) -> (Coreχ b n χ -> Doc ann) -> Definition b n χ -> Doc ann
pretty_def_builder pretty_bind pretty_name pretty_coreχ d =
  case d of
    (Mutualχ _ defs)  -> fold (fmap (pretty_bind . fst) defs) <+> fold (fmap (pretty_core . snd) defs)
    (SigDefχ _ _ _ _) -> "Signature"
    (IndDefχ _ _ _ _) -> "Co/Inductive type def"
    where
      pretty_core = pretty_core_builder pretty_bind pretty_name pretty_coreχ


pretty_core_builder :: (b n (Core b n χ) -> Doc ann) -> (n -> Doc ann) -> (Coreχ b n χ -> Doc ann) -> Core b n χ -> Doc ann
pretty_core_builder pretty_bind pretty_name pretty_coreχ c =
  case c of
    Coreχ v -> pretty_coreχ v
    Uniχ _ n -> "𝒰" <> pretty n
    Varχ _ name -> pretty_name name
      
    Prdχ _ _ _ -> align $ sep $ head tel : zipWith (<+>) (repeat "→") (tail tel)
      where
        tel = telescope c
        
        telescope (Prdχ _ bind e) = pretty_bind bind : telescope e
        telescope b = [pretty_core  b]
    
    Absχ _ bind e ->
      let (args, body) = telescope e
    
          telescope (Absχ _ bind e) =
            let (args, body) = telescope e in 
              (bind : args, body)
          telescope body = ([], body)
    
          pretty_args bind [] = pretty_bind bind
          pretty_args v (x : xs) = pretty_args v [] <+> pretty_args x xs
      in
        ("λ [" <> pretty_args bind args <> "]") <+> nest 2 (bracket body)
    -- telescoping
    Appχ χ l r -> sep $ fmap bracket $ unwind (Appχ χ l r)
    where 
        pretty_core = pretty_core_builder pretty_bind pretty_name pretty_coreχ
        bracket v = if iscore v then pretty_core v else "(" <> pretty_core v <> ")"
        
        iscore (Uniχ _ _) = True
        iscore (Varχ _ _) = True
        iscore _ = False
      
        unwind (Appχ _ l r) = unwind l <> [r]
        unwind t = [t]
