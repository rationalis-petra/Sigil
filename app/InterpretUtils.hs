module InterpretUtils
  ( eval_expr
  , eval_formula
  , eval_mod ) where

import Prelude hiding (mod)
import Control.Monad.Except (MonadError, throwError, catchError)
import Control.Lens ((^.))

import Data.Text (Text)
import qualified Data.Set as Set
import qualified Data.Map as Map
  
import Prettyprinter
import Prettyprinter.Render.Sigil

import Sigil.Parse
import Sigil.Abstract.Names
import Sigil.Abstract.Unify
import Sigil.Abstract.Syntax
import Sigil.Abstract.Substitution
import Sigil.Abstract.Environment
import Sigil.Interpret.Interpreter
import Sigil.Analysis.Typecheck
import Sigil.Analysis.FormulaCheck
import Sigil.Analysis.NameResolution
import Sigil.Concrete.Internal (InternalCore, InternalModule)


eval_expr :: forall m env s. (MonadError SigilDoc m, MonadGen m) =>
  Interpreter m SigilDoc env s -> Text -> [ImportDef] -> Text -> m (InternalCore, InternalCore)
eval_expr (Interpreter {..}) package_name imports line = do
  env <- get_env
  precs <- get_precs package_name imports
  resolution <- get_resolve package_name imports
  parsed <- core precs "playground" line  -- TODO: eof??
  resolved <- resolve_closed (("unbound name" <+>) . pretty) resolution parsed
    `catchError` (throwError . (<+>) "Resolution:")
  (term, ty) <- infer_core (CheckInterp eval norm_eq solve_formula spretty) env resolved
    `catchError` (throwError . (<+>) "Inference:")
  norm <- eval id (i_impl env) ty term
    `catchError` (throwError . (<+>) "Normalization:")
  pure (norm, ty)

eval_mod :: forall m env s. (MonadError SigilDoc m, MonadGen m) =>
  Interpreter m SigilDoc env s -> Text -> Text -> Text -> m InternalModule
eval_mod (Interpreter {..}) package_name filename modul_text = do
  parsed <- mod package_name (get_precs package_name) filename modul_text -- TODO: eof??
    `catchError` (throwError . (<+>) "Parse:")

  resolve_vars <- get_resolve package_name (parsed^.module_imports)
  resolved <- resolve_module
               (("unbound name" <+>) . pretty)
               (parsed^.module_header)
               (fmap Right resolve_vars) parsed
    `catchError` (throwError . (<+>) "Resolution:")

  env <- get_env
  check_module (CheckInterp eval norm_eq solve_formula spretty) env resolved
    `catchError` (throwError . (<+>) "Inference:")

  
eval_formula :: forall m env s. (MonadError SigilDoc m, MonadGen m) =>
  Interpreter m SigilDoc env s -> Text -> [ImportDef] -> Text -> m (Substitution Name InternalCore)
eval_formula (Interpreter {..}) package_name imports line = do
  env <- get_env
  precs <- get_precs package_name imports
  resolution <- get_resolve package_name imports
  parsed <- formula precs "playground" line  -- TODO: eof??
  resolved <- resolve_closed (("unbound name" <+>) . pretty) resolution parsed
    `catchError` (throwError . (<+>) "Resolution:")
  checked <- check_formula (CheckInterp eval norm_eq solve_formula spretty) env resolved
    `catchError` (throwError . (<+>) "Inference:")
  (Substitution solution) <- solve_formula id (i_impl env) checked
    `catchError` (throwError . (<+>) "Unification:")
  let exs = go checked
      go (Bind Exists n _ f) = Set.singleton n <> go f
      go (Bind Forall _ _ f) = go f
      go (And l r) = go l <> go r
      go (Conj _) = Set.empty
  pure $ Substitution $ Map.filterWithKey (\k _ -> Set.member k exs) solution
