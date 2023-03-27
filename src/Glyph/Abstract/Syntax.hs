module Glyph.Abstract.Syntax
  (Core(..),
   Module(..),
   ModuleDef(..),
   ImportDef(..),
   IndType(..),
   --Clause(..),
   Coreχ,
   Varχ,
   Uniχ,
   Prdχ,
   Absχ,
   Appχ) where


{----------------------------------- SYNTAX ------------------------------------}
{- This file contains definitions relating to the syntax                       -}
{- • Core   : The type of the core calculus                                    -}
{- • Module : The type of file-level modules.                                  -}
{- • Clause : Type of Seuth clauses                                            -}
{-                                                                             -}
{-------------------------------------------------------------------------------}


import Prelude hiding (lookup, length, head)

import Data.Text

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


data Core b v χ
  = Coreχ (Coreχ χ)
  -- The Core Calculus, based on Martin Löf
  | Uni (Uniχ χ) Int 
  | Var (Varχ χ) v
  | Prd (Prdχ χ) (b v (Core b v χ)) (Core b v χ)
  | Abs (Absχ χ) (b v (Core b v χ)) (Core b v χ)
  | App (Appχ χ) (Core b v χ) (Core b v χ)

  -- Type Families - with name and uid
  -- | Fam Text Integer [Core n χ]

  -- Inductive + Coinductive constants - with name and uid
  -- | Ive v Integer [Core n χ]
  -- | Cve [Core n χ]

  -- Records constants - with name and uid
  -- | Sct [(b (Core b v χ), Core b v χ)]
  -- | Sig [(b (Core b v χ), Core b v χ)]


type family Coreχ χ
type family Varχ χ
type family Uniχ χ
type family Prdχ χ
type family Absχ χ
type family Appχ χ

{---------------------------------- MODULE TYPE ----------------------------------}
{-                                                                               -}
{-                                                                               -}
{-                                                                               -}
{---------------------------------------------------------------------------------}

data Module b v χ  
  = Module { _module_name :: [Text]
           , _module_exports :: [Text]
           , _module_imports :: [ImportDef]
           , _module_defs :: [(b v (Core b v χ), ModuleDef b v χ)]
           } 

data ImportDef
  = ImportOne [Text] Text
  | ImportAll [Text] Text
  | ImportSet [Text] [Text]
  | ImportExcept [Text] [Text]
  

data IndType = Inductive | Coinductive  

data ModuleDef b v χ
  = SigDef IndType (b v (Core b v χ)) [(b v (Core b v χ))]
  | SctDef (b v (Core b v χ)) [(b v (Core b v χ))]
  | IndDef (b v (Core b v χ)) [(b v (Core b v χ))]
  | CoiDef (b v (Core b v χ)) [(b v (Core b v χ))]


{--------------------------------- EQ INSTANCE ---------------------------------}
{- The Equal type class instance performs an equality check directly on the    -}
{- names - this means that an Eq instance is only α equality if the name type  -}
{- is a Debruijn index.                                                        -}
{-------------------------------------------------------------------------------}


instance (Eq (b v (Core b v χ)), Eq v, Eq (Coreχ χ)) => Eq (Core b v χ) where
  v1 == v2 = case (v1, v2) of 
    (Coreχ r, Coreχ r') -> r == r'
    (Uni _ n, Uni _ n') -> n == n'
    (Var _ n, Var _ n') -> n == n'
    (Prd _ x t, Prd _ x' t') ->
      x == x' && t == t'
    (Abs _ x e, Abs _ x' e') ->
      x == x' && e == e'
    (App _ l r, App _ l' r') ->
      l == l' && r == r'
    (_, _) -> False


{------------------------------ PRETTY PRINTING --------------------------------}
{-     Instances for printing syntax trees to via the Prettyprinter library    -}
{-------------------------------------------------------------------------------}

instance (Pretty (b v (Core b v χ)), Pretty v, Pretty (Coreχ χ)) => Pretty (Core b v χ) where
  pretty c = case c of  
    Coreχ v -> pretty v
    Uni _ n -> "𝒰" <> pretty n
    Var _ name -> pretty name
 
    Prd _ bind b -> ("(" <> pretty bind <> " ) → ") <+> pretty b
    Abs _ bind e ->
      let (args, body) = telescope e
    
          telescope (Abs _ bind e) =
            let (args, body) = telescope e in 
              (bind : args, body)
          telescope body = ([], body)
    
          pretty_args bind [] = pretty bind
          pretty_args v (x : xs) = pretty_args v [] <+> pretty_args x xs
      in
        ("λ [" <> pretty_args bind args <> "]") <+> pretty body
    App _ l r -> pretty l <+> pretty r
