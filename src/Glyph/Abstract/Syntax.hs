module Glyph.Abstract.Syntax
  ( Core(..)
  , Module(..)
  , Definition(..)
  , ImportDef(..)
  , IndType(..)
   --Clause(..),
  , Forallχ
  , Coreχ
  , Varχ
  , Uniχ
  , Prdχ
  , Absχ
  , Appχ ) where


{----------------------------------- SYNTAX ------------------------------------}
{- This file contains definitions relating to the syntax                       -}
{- • Core   : The type of the core calculus                                    -}
{- • Module : The type of file-level modules.                                  -}
{- • Clause : Type of Seuth clauses                                            -}
{-                                                                             -}
{-------------------------------------------------------------------------------}


import Prelude hiding (lookup, length, head)

import Data.Kind
import Data.Foldable
import Data.Text hiding (zipWith)

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
  | Uni (Uniχ χ) Int 
  | Var (Varχ χ) n
  | Prd (Prdχ χ) (b n (Core b n χ)) (Core b n χ)
  | Abs (Absχ χ) (b n (Core b n χ)) (Core b n χ)
  | App (Appχ χ) (Core b n χ) (Core b n χ)

  -- Type Families - with name and uid
  -- | Fam Text Integer [Core n χ]

  -- Inductive + Coinductive constants - with name and uid
  -- | Ive v Integer [Core n χ]
  -- | Cve [Core n χ]

  -- Records constants - with name and uid
  -- | Sct [(b (Core b v χ), Core b v χ)]
  -- | Sig [(b (Core b v χ), Core b v χ)]


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
  = Mutual [(b n (Core b n χ), Core b n χ)]
  | SigDef IndType (b n (Core b n χ)) [(b n (Core b n χ))]
  | IndDef IndType (b n (Core b n χ)) [(b n (Core b n χ))]
  -- | SctDef (b n (Core b n χ)) [(b n (Core b n χ))]


{--------------------------------- EQ INSTANCE ---------------------------------}
{- The Equal type class instance performs an equality check directly on the    -}
{- names - this means that an Eq instance is not α equality!                   -}
{- Use the Term typeclass for α-equality                                       -}
{-------------------------------------------------------------------------------}


instance (Forall Eq b n χ) --Eq (b n (Core b n χ)), Eq n, Forallχ Eq χ, Eq (Coreχ b n χ))
          => Eq (Definition b n χ) where
  v1 == v2 = case (v1, v2) of 
    (Mutual defs, Mutual defs') -> defs == defs'
    (SigDef itype bind fields, SigDef itype' bind' fields') ->
      itype == itype' && bind == bind' && fields == fields'
    (IndDef itype bind terms, IndDef itype' bind' terms') ->
      itype == itype' && bind == bind' && terms == terms'
    (_, _) -> False

instance Forall Eq b n χ --(Eq (b n (Core b n χ)), Eq n, Forallχ Eq χ, Eq (Coreχ b n χ))
         => Eq (Core b n χ) where
  v1 == v2 = case (v1, v2) of 
    (Coreχ r, Coreχ r') ->
      r == r'
    (Uni χ n, Uni χ' n') ->
      χ == χ' && n == n'
    (Var χ n, Var χ' n') ->
      χ == χ' && n == n' 
    (Prd χ x t, Prd χ' x' t') ->
      χ == χ' && x == x' && t == t' 
    (Abs χ x e, Abs χ' x' e') ->
      χ == χ' && x == x' && e == e'  
    (App χ l r, App χ' l' r') ->
      χ == χ' && l == l' && r == r'
    (_, _) -> False


{------------------------------ PRETTY PRINTING --------------------------------}
{-     Instances for printing syntax trees to via the Prettyprinter library    -}
{-------------------------------------------------------------------------------}


instance (Pretty (b n (Core b n χ)), Pretty n, Pretty (Coreχ b n χ)) => Pretty (Definition b n χ) where
  pretty d = case d of
    (Mutual defs)  -> fold (fmap (pretty . fst) defs) <+> fold (fmap (pretty . snd) defs)
    (SigDef _ _ _) -> "Signature"
    (IndDef _ _ _) -> "Co/Inductive type def"


instance (Pretty (b n (Core b n χ)), Pretty n, Pretty (Coreχ b n χ)) => Pretty (Core b n χ) where
  pretty c = case c of  
    Coreχ v -> pretty v
    Uni _ n -> "𝒰" <> pretty n
    Var _ name -> pretty name
 
    Prd _ _ _ -> align $ sep $ zipWith (<+>) ("" : repeat "→") (telescope c)
      where
        telescope (Prd _ bind e) = pretty bind : telescope e
        telescope b = [pretty b]
  
    Abs _ bind e ->
      let (args, body) = telescope e
    
          telescope (Abs _ bind e) =
            let (args, body) = telescope e in 
              (bind : args, body)
          telescope body = ([], body)
    
          pretty_args bind [] = pretty bind
          pretty_args v (x : xs) = pretty_args v [] <+> pretty_args x xs
      in
        ("λ [" <> pretty_args bind args <> "]") <+> nest 2 (pretty body)
    App _ l r -> pretty l <+> pretty r
