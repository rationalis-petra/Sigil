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


eval_expr :: forall m e s t f. (MonadError SigilDoc m, MonadGen m, Environment Name e) =>
  Interpreter m SigilDoc (e (Maybe InternalCore, InternalCore)) s t f -> Text -> [ImportDef] -> Text -> m (InternalCore, InternalCore)
eval_expr i@(Interpreter {..}) package_name imports line = do
  env <- get_env package_name imports
  precs <- get_precs package_name imports
  resolution <- get_resolve package_name imports
  parsed <- core precs "playground" line  -- TODO: eof??
  resolved <- resolve_closed (("unbound name" <+>) . pretty) resolution parsed
    `catchError` (throwError . (<+>) "Resolution:")
  (term, ty) <- infer (CheckInterp (interp_eval i) (interp_eq i) spretty) env resolved
    `catchError` (throwError . (<+>) "Inference:")
  norm <- (interp_eval i) id env ty term
    `catchError` (throwError . (<+>) "Normalization:")
  pure (norm, ty)

eval_mod :: forall m e s t f. (MonadError SigilDoc m, MonadGen m, Environment Name e) =>
  Interpreter m SigilDoc (e (Maybe InternalCore, InternalCore)) s t f -> Text -> Text -> Text -> m InternalModule
eval_mod i@(Interpreter {..}) package_name filename modul_text = do
  parsed <- mod (get_precs package_name) filename modul_text -- TODO: eof??
    `catchError` (throwError . (<+>) "Parse:")

  resolve_vars <- get_resolve package_name (parsed^.module_imports)
  resolved <- resolve_module
               (("unbound name" <+>) . pretty)
               (parsed^.module_header)
               (fmap Right resolve_vars) parsed
    `catchError` (throwError . (<+>) "Resolution:")

  env <- get_env package_name (parsed^.module_imports)
  check_module (CheckInterp (interp_eval i) (interp_eq i) spretty) env resolved
    `catchError` (throwError . (<+>) "Inference:")

  
eval_formula :: forall m e s t f. (MonadError SigilDoc m, MonadGen m, Environment Name e) =>
  Interpreter m SigilDoc (e (Maybe InternalCore, InternalCore)) s t f -> Text -> [ImportDef] -> Text -> m (Substitution Name InternalCore)
eval_formula i@(Interpreter {..}) package_name imports line = do
  env <- get_env package_name imports
  precs <- get_precs package_name imports
  resolution <- get_resolve package_name imports
  parsed <- formula precs "playground" line  -- TODO: eof??
  resolved <- resolve_closed (("unbound name" <+>) . pretty) resolution parsed
    `catchError` (throwError . (<+>) "Resolution:")
  checked <- check_formula (CheckInterp (interp_eval i) (interp_eq i) spretty) env resolved
    `catchError` (throwError . (<+>) "Inference:")
  (Substitution solution) <- (interp_solve i) id env checked
    `catchError` (throwError . (<+>) "Unification:")
  let exs = go checked
      go (Bind Exists n _ f) = Set.singleton n <> go f
      go (Bind Forall _ _ f) = go f
      go (And l r) = go l <> go r
      go (Conj _) = Set.empty
  pure $ Substitution $ Map.filterWithKey (\k _ -> Set.member k exs) solution

-- Internal Use only 
interp_eval :: forall m e s t f. (MonadError SigilDoc m) =>
          Interpreter m SigilDoc (e (Maybe InternalCore, InternalCore)) s t f
            -> (SigilDoc -> SigilDoc) -> e (Maybe InternalCore, InternalCore) -> InternalCore -> InternalCore -> m InternalCore
interp_eval (Interpreter {..}) f env ty val = do
    ty' <- reify ty
    val' <- reify val
    result <- eval f env ty' val'
    reflect result

interp_solve :: forall m e s t f. (MonadError SigilDoc m) =>
          Interpreter m SigilDoc (e (Maybe InternalCore, InternalCore)) s t f
            -> (SigilDoc -> SigilDoc) -> e (Maybe InternalCore, InternalCore) -> Formula Name InternalCore -> m (Substitution Name InternalCore)
interp_solve (Interpreter {..}) f env formula = do
    formula' <- reify_formula formula
    subst <- solve_formula f env formula'
    mapM reflect subst 

interp_eq :: forall m e s t f. (MonadError SigilDoc m) =>
          Interpreter m SigilDoc (e (Maybe InternalCore, InternalCore)) s t f
            -> (SigilDoc -> SigilDoc) -> e (Maybe InternalCore, InternalCore) -> InternalCore -> InternalCore -> InternalCore -> m Bool
interp_eq (Interpreter {..}) f env ty l r = do
    ty' <- reify ty
    l' <- reify l
    r' <- reify r
    norm_eq f env ty' l' r'

