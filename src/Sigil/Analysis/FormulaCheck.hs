module Sigil.Analysis.FormulaCheck
  ( check_formula ) where

import Control.Monad.Except (MonadError, throwError)

import Prettyprinter

import Sigil.Abstract.Names
import Sigil.Abstract.Unify
import Sigil.Abstract.Environment
import Sigil.Analysis.Typecheck
import Sigil.Concrete.Resolved
import Sigil.Concrete.Decorations.Range
import Sigil.Concrete.Internal


check_formula :: (MonadGen m, MonadError err m)
  => CheckInterp m err env -> Env env m
  -> Formula Name ResolvedCore -> m (Formula Name InternalCore)
check_formula interp@(CheckInterp {..}) env formula = case formula of 
  Conj scons -> Conj <$> mapM (check_scons interp env) scons
  And l r -> And <$> check_formula interp env l <*> check_formula interp env r
  Bind q n ty f -> do
    (ty', kind) <- infer interp env ty
    ty_norm <- normalize (lift_err . flip NormErr mempty) (i_impl env) kind ty'
    env' <- insert n (Nothing, ty_norm) env
    Bind q n ty_norm <$> check_formula interp env' f 


check_scons :: (MonadGen m, MonadError err m)
  => CheckInterp m err env -> Env env m
  -> SingleConstraint ResolvedCore -> m (SingleConstraint InternalCore)
check_scons interp@(CheckInterp {..}) env cons = case cons of
  (l :≗: r) -> do
    (l', lty) <- infer interp env l
    (r', rty) <- infer interp env r
    n <- get_universe lift_err (range l <> range r) env lty
    check_eq mempty interp env (Uni n) lty rty
    l_norm <- normalize (lift_err . flip NormErr mempty) (i_impl env) lty l'
    r_norm <- normalize (lift_err . flip NormErr mempty) (i_impl env) rty r'
    pure $ (l_norm :≗: r_norm)
  (val :∈: ty) -> do
    (ty', kind) <- infer interp env ty
    ty_norm <- normalize (lift_err . flip NormErr mempty) (i_impl env) kind ty'
    val' <- check interp env val ty_norm
    val_norm <- normalize (lift_err . flip NormErr mempty) (i_impl env) ty_norm val'
    pure $ (val_norm :∈: ty_norm)


check_eq :: (MonadError err m) => Range -> (CheckInterp m err env) -> Env env m -> InternalCore -> InternalCore -> InternalCore -> m ()
check_eq range (CheckInterp {..}) env ty l r
 = 
  αβη_eq (lift_err . flip NormErr range) (i_impl env) ty l r >>= \case
    True -> pure ()
    False -> throwError $ lift_err $ PrettyErr ("not-equal:" <+> pretty l <+> "and" <+> pretty r) range
