module Sigil.Interpret.Canonical.Values
  ( Sem(..)
  , Neutral(..)
  , Normal(..)
  , SemTel
  , SemModule(..)
  , SemPackage(..)
  , SemEnv
  , insert
  , path_lookup
  , lookup_err
  ) where

import Control.Monad.Except (MonadError, throwError)
import qualified Data.Map as Map
import Data.Map (Map)
import Data.Text (Text)
import Data.Kind
import Data.List (find)

import Prettyprinter

import Sigil.Abstract.Names  
import Sigil.Abstract.Environment hiding (insert)
import Sigil.Abstract.Syntax  
import Sigil.Concrete.Decorations.Implicit (ArgType(..))

type SemEnv m = (Map UniqueName (Sem m), Map Text (SemPackage m))

data Sem m
  = SUni Integer
  | SPrd ArgType Name (Sem m) (Sem m)
  | SAbs Name (Sem m) (Sem m -> m (Sem m))
  | SInd Name (Sem m) [(Text, Sem m -> m (Sem m))]
  | SCtr Text (Sem m) [Sem m]
  | SEql (SemTel m) (Sem m) (Sem m) (Sem m)
  | SDap (SemTel m) (Sem m)
  | STrL (SemTel m) (Sem m) (Sem m)
  | STrR (SemTel m) (Sem m) (Sem m)
  | Neutral (Sem m) (Neutral m)

data Neutral m
  = NeuVar Name
  | NeuApp (Neutral m) (Normal m)
  | NeuDap (SemTel m) (Neutral m) -- A neutral explicit substitution, must be empty!
  | NeuRec Name (Sem m) (Neutral m)
    [(Sem m -> Maybe (m (Sem m)), m (Pattern Name, Sem m))]

data Normal (m :: Type -> Type) = Normal (Sem m) (Sem m)

type SemTel m = [(Name, (Sem m, Sem m, Sem m), Sem m)]

data SemModule m = SemModule
  { smimports :: [ImportDef]
  , smexports :: [ExportDef]
  , smdefs :: [(Text, Sem m)]
  }

data SemPackage m = SemPackage
  { sprequires :: [Text]
  , spprovides :: [Text]
  , spmodules :: MTree (SemModule m)
  }

insert :: Name -> Sem m -> SemEnv m -> SemEnv m
insert (Name n) val (e1, e2) = case n of
  Right qn -> (Map.insert qn val e1, e2)
  Left _ -> error "trying to insert unqualified name"

path_lookup :: Path -> Map Text (SemPackage m) -> Maybe (Sem m)
path_lookup (Path (package_name, path)) env = case Map.lookup package_name env of
  Just spackage -> case get_modulo_path path (spmodules spackage) of
    Just (smodule, [n]) ->
      let
        has_name name (name', _)
          | name == name' = True
          | otherwise = False
      in case find (has_name n) (smdefs smodule) of
        Just (_,val) -> Just val
        Nothing -> Nothing
    _ -> Nothing
  _ -> Nothing

lookup_err :: MonadError err m => (Doc ann -> err) -> Name -> SemEnv m -> m (Sem m)
lookup_err lift_err n (e1, e2) =
  let res = case n of
        Name (Right un) -> Map.lookup un e1
        Name (Left qn) -> path_lookup qn e2
  in case res of
    Just v -> pure v
    Nothing -> throwError $ lift_err $ "Couldn't find variable: " <+> pretty n

{------------------------------- PRETTY INSTANCES ------------------------------}
{- Pretty                                                                      -}
{-                                                                             -}
{-------------------------------------------------------------------------------}


instance Pretty (Sem m) where
  pretty sem = case sem of 
    SUni n -> "𝕌" <> pretty_subscript n
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
    SPrd at n a b -> case at of
      Regular -> "(" <> pretty n <+> "⮜" <+> pretty a <> ")" <+> "→" <+> pretty b
      Implicit -> "⟨" <> pretty n <+> "⮜" <+> pretty a <> ")" <+> "→" <+> pretty b
    SAbs n _ _ -> "λ (" <> pretty n <> ")" <+> "..."
    SEql tel ty a b -> "ι" <+> pretty_tel tel <+> pretty ty <+> pretty a <+> pretty b
    SDap tel val -> "ρ" <+> pretty_tel tel <+> pretty val

    SInd nm val ctors ->
      "μ" <+> pretty nm <+> "⮜" <+> pretty val
      <+> nest 2 (vsep (map (\(l,_) -> pretty l <+> "⮜" <+> "...") ctors))
    SCtr label _ vals -> pretty (":" <> label) <+> sep (map pretty vals)
    STrL tel ty val -> "⍃" <+> pretty_tel tel <+> pretty ty <+> pretty val
    STrR tel ty val -> "⍄" <+> pretty_tel tel <+> pretty ty <+> pretty val

    Neutral _ n -> pretty n
    where 
      pretty_tel [(name, (ty, v1, v2), id)] = 
        pretty name <+> "⮜" <+> pretty ty <+> ("(" <> pretty v1 <+> "=" <+> pretty v2 <> ")") <+> "≜" <+> pretty id
      pretty_tel ((name, (ty, v1, v2), id) : tel) = 
        pretty name <+> "⮜" <+> pretty ty <+> ("(" <> pretty v1 <+> "=" <+> pretty v2 <> ")") <+> "≜" <+> pretty id
             <+> "," <+> pretty_tel tel
      pretty_tel [] = "."

instance Pretty (Neutral m) where
  pretty neu = case neu of
    NeuVar n -> pretty n
    NeuApp l r -> pretty l <+> pretty r
    NeuDap _ val -> "ρ …." <+> pretty val
    NeuRec name rty val _ ->
      vsep [ "φ" <+> pretty name <+> "⮜" <+> pretty rty <> "," <+> pretty val <> "."
           , nest 2 "..."
           ] 
        
instance Pretty (Normal m) where
  pretty (Normal _ val) = pretty val
