module InterpretUtils
  ( eval_expr
  , eval_mod ) where

import Prelude hiding (mod)
import Control.Monad.Except (MonadError, throwError, catchError)
import Control.Lens ((^.))

import Data.Text (Text)
  
import Prettyprinter
import Prettyprinter.Render.Sigil

import Sigil.Parse
import Sigil.Abstract.Names
import Sigil.Abstract.Syntax
import Sigil.Abstract.Environment
import Sigil.Interpret.Interpreter
import Sigil.Analysis.Typecheck
import Sigil.Analysis.NameResolution
import Sigil.Concrete.Internal (InternalCore, InternalModule)

eval_expr :: forall m e s t. (MonadError SigilDoc m, MonadGen m, Environment Name e) =>
  Interpreter m SigilDoc (e (Maybe InternalCore, InternalCore)) s t -> Text -> [ImportDef] -> Text -> m (InternalCore, InternalCore)
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

eval_mod :: forall m e s t. (MonadError SigilDoc m, MonadGen m, Environment Name e) =>
  Interpreter m SigilDoc (e (Maybe InternalCore, InternalCore)) s t -> Text -> Text -> Text -> m InternalModule
eval_mod i@(Interpreter {..}) package_name modulename modul = do
  parsed <- mod (get_precs package_name) modulename modul -- TODO: eof??
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

-- Internal Use only 
interp_eval :: forall m e s t. (MonadError SigilDoc m) =>
          Interpreter m SigilDoc (e (Maybe InternalCore, InternalCore)) s t
            -> (SigilDoc -> SigilDoc) -> e (Maybe InternalCore, InternalCore) -> InternalCore -> InternalCore -> m InternalCore
interp_eval (Interpreter {..}) f env ty val = do
    ty' <- reify ty
    val' <- reify val
    result <- eval f env ty' val'
    reflect result

interp_eq :: forall m e s t. (MonadError SigilDoc m) =>
          Interpreter m SigilDoc (e (Maybe InternalCore, InternalCore)) s t
            -> (SigilDoc -> SigilDoc) -> e (Maybe InternalCore, InternalCore) -> InternalCore -> InternalCore -> InternalCore -> m Bool
interp_eq (Interpreter {..}) f env ty l r = do
    ty' <- reify ty
    l' <- reify l
    r' <- reify r
    norm_eq f env ty' l' r'

