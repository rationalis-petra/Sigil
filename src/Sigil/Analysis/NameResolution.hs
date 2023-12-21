module Sigil.Analysis.NameResolution
  ( ResolveTo(..)
  , resolve_closed
  , resolve_module
  ) where


import Prelude hiding (lookup)
import Control.Lens
import Control.Monad.Except (MonadError, throwError)
import qualified Data.List.NonEmpty as NonEmpty
import Data.List.NonEmpty ()
import Data.Map (Map, lookup, insert)
import Data.Text (Text)
import Data.List.NonEmpty (NonEmpty(..))

import Sigil.Abstract.Names
import Sigil.Abstract.Syntax
import Sigil.Abstract.Unify

import Sigil.Concrete.Parsed
import Sigil.Concrete.Resolved


{--------------------------------- RESOLUTION ----------------------------------}
{-                                                                             -}
{-                                                                             -}
{-                                                                             -}
{-------------------------------------------------------------------------------}

class ResolveTo a b | a -> b where
  resolve :: (MonadGen m, MonadError err m) => (Text -> err) -> Map Text (Either Integer QualName) -> a -> m b

resolve_closed :: (MonadGen m, MonadError err m, ResolveTo a b) => (Text -> err) -> Map Text QualName -> a -> m b
resolve_closed lift_err rmap = resolve lift_err (fmap Right rmap)

instance ResolveTo a b => ResolveTo (a, a, a) (b, b, b) where
  resolve lift_err vars (x, y, z) = (,,) <$> rv x <*> rv y <*> rv z
    where rv = resolve lift_err vars

instance ResolveTo ParsedCore ResolvedCore where
  resolve lift_err vars term = case term of 
    Core -> pure $ Coreχ ()
    Uni rn n -> pure $ Uniχ rn n
    Var rn name -> case lookup name vars of
      Just (Left n) -> pure $ Varχ rn $ Name $ Right (n, name)
      Just (Right q) -> pure $ Varχ rn $ Name $ Left q
      Nothing -> throwError $ lift_err name
    Prd rn at (OptBind (t, a)) ty -> do
      id <- fresh_id
      let n = (\text -> Name $ Right (id,text)) <$> t
          vars' = maybe vars (\t -> insert t (Left id) vars) t
      a' <- mapM (resolve lift_err vars) a
      Prdχ (rn, at) (OptBind (n, a')) <$> resolve lift_err vars' ty
    Abs rn at (OptBind (t, ty)) e -> do
      id <- fresh_id
      let
        n = (\text -> Name $ Right (id,text)) <$> t 
        vars' = maybe vars (\t -> insert t (Left id) vars) t
      ty' <- mapM (resolve lift_err vars) ty
      Absχ (rn,at) (OptBind (n, ty')) <$> resolve lift_err vars' e
    App rn l r -> Appχ rn <$> resolve lift_err vars l <*> resolve lift_err vars r
    Ind rn text msort ctors -> do
      id <- fresh_id 
      let n = Name $ Right (id, text)
          vars' = insert text (Left id) vars
      msort' <- mapM (resolve lift_err vars) msort
      Indχ rn n msort' <$> mapM (resolve_ctor vars') ctors
      where 
        resolve_ctor vars (label, ty) =
          (label,) <$> resolve lift_err vars ty
    Ctr rn label ty -> Ctrχ rn label <$> mapM (resolve lift_err vars) ty
    Rec rn (OptBind (n, a)) val cases -> do
      id <- fresh_id 
      let n' = (\text -> Name $ Right (id, text)) <$> n
          vars' = maybe vars (\t -> insert t (Left id) vars) n
      a' <- mapM (resolve lift_err vars) a 
      val' <- resolve lift_err vars val 
      cases' <- mapM (resolve_case vars') cases
      pure $ Recχ rn (OptBind (n', a')) val' cases'
      where 
        resolve_case vars (pat, val) = do
          (pat', vars') <- update_pat vars pat
          (pat', ) <$> resolve lift_err vars' val

        update_pat vars = \case 
          PatCtr n subpats -> do
            (subpats', vars') <- foldr (\p m -> do
                                           (ps, vars') <- m
                                           (p', vars'') <- update_pat vars' p
                                           pure (p':ps, vars'')) (pure ([], vars)) subpats
            pure $ (PatCtr n subpats', vars')
          PatVar n -> do
            id <- fresh_id
            let p' = PatVar $ Name $ Right $ (id, n)
            pure $ (p', insert n (Left id) vars)

    Eql rn tel ty a a' -> do
      (vars', tel') <- resolve_tel vars tel
      Eqlχ rn tel' <$> resolve lift_err vars' ty <*> resolve lift_err vars' a <*> resolve lift_err vars' a'
    ETC rn val -> do
      ETCχ rn <$> resolve lift_err vars val
    CTE rn val -> do
      CTEχ rn <$> resolve lift_err vars val

    Dap rn tel val -> do
      (vars', tel') <- resolve_tel vars tel
      Dapχ rn tel' <$> resolve lift_err vars' val
    TrL rn tel ty val -> do
      (vars', tel') <- resolve_tel vars tel
      TrLχ rn tel' <$> resolve lift_err vars' ty <*> resolve lift_err vars' val
    TrR rn tel ty val -> do
      (vars', tel') <- resolve_tel vars tel
      TrRχ rn tel' <$> resolve lift_err vars' ty <*> resolve lift_err vars' val
    LfL rn tel ty val -> do
      (vars', tel') <- resolve_tel vars tel
      LfLχ rn tel' <$> resolve lift_err vars' ty <*> resolve lift_err vars' val
    LfR rn tel ty val -> do
      (vars', tel') <- resolve_tel vars tel
      LfRχ rn tel' <$> resolve lift_err vars' ty <*> resolve lift_err vars' val

    where
      resolve_tel vars [] = pure (vars, [])
      resolve_tel vars ((OptBind (t, a), val) : tel) = do
        id <- fresh_id 
        let n = (\text -> Name $ Right (id, text)) <$> t
            vars' = maybe vars (\t -> insert t (Left id) vars) t
        a' <- mapM (resolve lift_err vars) a 
        val' <- resolve lift_err vars' val 
        (vars'', tel') <- resolve_tel vars' tel
        pure $ (vars'', ((OptBind (n, a'), val') : tel'))

instance ResolveTo (SingleConstraint ParsedCore) (SingleConstraint ResolvedCore) where
  resolve lift_err vars cons = case cons of 
    (l :≗: r) -> (:≗:) <$> resolve lift_err vars l <*> resolve lift_err vars r
    (l :∈: r) -> (:∈:) <$> resolve lift_err vars l <*> resolve lift_err vars r

instance ResolveTo (Formula Text ParsedCore) (Formula Name ResolvedCore) where
  resolve lift_err vars formula = case formula of 
    Conj cons -> Conj <$> mapM (resolve lift_err vars) cons
    And l r -> And <$> resolve lift_err vars l <*> resolve lift_err vars r
    Bind q text ty f -> do
      id <- fresh_id 
      let n = Name $ Right (id, text)
          vars' = insert text (Left id) vars
      ty' <- resolve lift_err vars ty
      f' <- resolve lift_err vars' f
      pure $ Bind q n ty' f'


resolve_entry :: (MonadGen m, MonadError err m) => (Text -> err) -> Path -> Map Text (Either Integer QualName) -> ParsedEntry -> m ResolvedEntry
resolve_entry lift_err path vars entry = case entry of
  Singleχ rn (OptBind (t,a)) val -> do
    let qn = (path <>) . Path . (:| []) <$> t
        n = Name . Left . unPath <$> qn
        vars' = case (t, qn) of
          (Just tx, Just nm) -> insert tx (Right $ unPath nm) vars
          _ -> vars
    a' <- mapM (resolve lift_err vars) a
    val' <- resolve lift_err vars' val
    pure $ Singleχ rn (OptBind (n, a')) val'


-- TODO: interface with environment somehow? (based on imports/exports)
resolve_module :: (MonadGen m, MonadError err m) => (Text -> err) -> Path -> Map Text (Either Integer QualName) -> ParsedModule -> m ResolvedModule
resolve_module lift_err path vars modul = do
  entries' <- resolve_entries vars (modul^.module_entries)
  pure $ (module_entries .~ entries') modul

  where 
    --resolve_entries :: (MonadGen m, MonadError err m) => Map Text (Either Integer QualName) -> [ParsedEntry] -> m [ResolvedEntry]
    resolve_entries _ [] = pure []
    resolve_entries vars (e:es) = do
      e' <- resolve_entry lift_err path vars e
      let vars' = update_vars vars e'
      (e' :) <$> resolve_entries vars' es

    update_vars vars entry = case entry of 
      Singleχ _ (OptBind (n,_)) _ -> do
        maybe vars (\(nm, txt) -> insert txt nm vars) (get_local_name <$> n)

    get_local_name (Name (Right (id, text))) = (Left id, text)
    get_local_name (Name (Left p)) = (Right p, NonEmpty.last p)
