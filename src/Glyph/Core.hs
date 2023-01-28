module Glyph.Core (
  Core(..),
  Coreχ,
  Varχ,
  Uniχ,
  Prdχ,
  Absχ,
  Appχ)
  where

import Prelude hiding (lookup, length, head)
import Data.Text (Text)
import Prettyprinter


{---------------------------------- CORE TYPE ----------------------------------}
{- The Core Type represents the core calculus upon which Glyph is based. It is -}
{- the primary Representation of Syntax used within the Compiler   .           -}
{-                                                                             -}
{- Core takes two type parameters, n and χ, which serve the following purpose: -}
{- • n represents the type of names, and might change when:                    -}
{-   • Representing metavariables in unification                               -}
{-   • Representing names which have not yet been resolved after parsing       -}
{-   • Representing names amenable to α-equivalence (e.g. DeBruijn indices)    -}
{- • χ is used as part of the 'trees that grow' idiom, and is used to make     -}
{-   variants of the syntax tree. Variants can include extra nodes or attach   -}
{-   extra information to each node, e.g.                                      -}
{-   • Keeping track of the source file a value came from                      -}
{-   • Adding extra type information to a node                                 -}
{-   • Adding a new node for constants (numbers etc.)                          -}
{-                                                                             -}


data Core n χ
  = Coreχ (Coreχ χ)
  | Uni (Uniχ χ) Int 
  | Var (Varχ χ) n
  | Prd (Prdχ χ) Text (Core n χ) (Core n χ)
  | Abs (Absχ χ) Text (Core n χ)
  | App (Appχ χ) (Core n χ) (Core n χ)

type family Coreχ χ
type family Varχ χ
type family Uniχ χ
type family Prdχ χ
type family Absχ χ
type family Appχ χ


{--------------------------------- EQ INSTANCE ---------------------------------}
{- The Equal type class instance performs an equality check directly on the    -}
{- names - this means that an Eq instance is only α equality if the name type  -}
{- is a Debruijn index.                                                        -}


instance (Eq n, Eq (Coreχ χ)) => Eq (Core n χ) where
  v1 == v2 = case (v1, v2) of 
    (Coreχ r, Coreχ r') -> r == r'
    (Uni _ n, Uni _ n') -> n == n'
    (Var _ n, Var _ n') -> n == n'
    (Prd _ x a b, Prd _ x' a' b') ->
      x == x' && a == a' && b == b'
    (Abs _ x e, Abs _ x' e') ->
      x == x' && e == e'
    (App _ l r, App _ l' r') ->
      l == l' && r == r'
    (_, _) -> False


{------------------------------ PRETTY PRINTING --------------------------------}
{- Instances for printing syntax trees to via the Prettyprinter library        -}

instance (Pretty n, Pretty (Coreχ χ)) => Pretty (Core n χ) where
  pretty c = case c of  
    Coreχ v -> pretty v
    Uni _ n -> "𝒰" <> pretty n
    Var _ name -> pretty name
 
    Prd _ var a b -> pretty ("(" <> var) <+> ":" <+> pretty a <+> " ) → " <+> pretty b
    Abs _ var e ->
      let (args, body) = telescope e
    
          telescope (Abs _ var e) =
            let (args, body) = telescope e in 
              (var : args, body)
          telescope body = ([], body)
    
          pretty_args var [] = pretty var
          pretty_args v (x : xs) = pretty_args v [] <+> pretty_args x xs
      in
        ("λ [" <> pretty_args var args <> "]") <+> pretty body
    App _ l r -> pretty l <+> pretty r
