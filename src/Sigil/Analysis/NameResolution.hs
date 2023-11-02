module Sigil.Analysis.NameResolution
  ( ResolveTo(..)
  , resolve_closed
  , resolve_module
  ) where


import Prelude hiding (lookup)
import Control.Lens
import qualified Data.List.NonEmpty as NonEmpty
import Data.List.NonEmpty ()
import Data.Map (Map, lookup, insert)
import Data.Text (Text, unpack)
import Data.Foldable (foldl')
import Data.List.NonEmpty (NonEmpty(..))

import Sigil.Abstract.Names
import Sigil.Abstract.Syntax

import Sigil.Concrete.Parsed
import Sigil.Concrete.Resolved


{--------------------------------- RESOLUTION ----------------------------------}
{-                                                                             -}
{-                                                                             -}
{-                                                                             -}
{-------------------------------------------------------------------------------}

class ResolveTo a b | a -> b where
  resolve :: MonadGen m => Map Text (Either Integer QualName) -> a -> m b

resolve_closed :: (MonadGen m, ResolveTo a b) => Map Text QualName -> a -> m b
resolve_closed rmap = resolve (fmap Right rmap)

instance ResolveTo a b => ResolveTo (a, a, a) (b, b, b) where
  resolve vars (x, y, z) = (,,) <$> rv x <*> rv y <*> rv z
    where rv = resolve vars

instance ResolveTo ParsedCore ResolvedCore where
  resolve vars term = case term of 
    Core -> pure $ Coreχ ()
    Uni rn n -> pure $ Uniχ rn n
    Var rn name -> case lookup name vars of
      Just (Left n) -> pure $ Varχ rn $ Name $ Right (n, name)
      Just (Right q) -> pure $ Varχ rn $ Name $ Left q
      Nothing -> error (unpack $ "bad name: " <> name) -- pure $ Varχ rn $ Name $ Left (name :| [])
    Prd rn (OptBind (t, a)) ty -> do
      id <- fresh_id
      let n = (\text -> Name $ Right (id,text)) <$> t
          vars' = maybe vars (\t -> insert t (Left id) vars) t
      a' <- mapM (resolve vars) a
      Prdχ rn (OptBind (n, a')) <$> resolve vars' ty
    Abs rn (OptBind (t, ty)) e -> do
      id <- fresh_id
      let
        n = (\text -> Name $ Right (id,text)) <$> t 
        vars' = maybe vars (\t -> insert t (Left id) vars) t
      ty' <- mapM (resolve vars) ty
      Absχ rn (OptBind (n, ty')) <$> resolve vars' e
    App rn l r -> Appχ rn <$> resolve vars l <*> resolve vars r
    Eql rn tel ty a a' -> do
      (vars', tel') <- resolve_tel vars tel
      Eqlχ rn tel' <$> resolve vars' ty <*> resolve vars' a <*> resolve vars' a'
    Dap rn tel val -> do
      (vars', tel') <- resolve_tel vars tel
      Dapχ rn tel' <$> resolve vars' val
    Ind rn (OptBind (t, a)) ctors -> do
      id <- fresh_id 
      let n = (\text -> Name $ Right (id, text)) <$> t
          vars' = maybe vars (\t -> insert t (Left id) vars) t
      a' <- mapM (resolve vars) a
      Indχ rn (OptBind (n, a')) <$> mapM (resolve_ctor vars') ctors
      where 
        resolve_ctor vars (label, OptBind (n, ty)) = do
          id <- fresh_id
          let n' = (\text -> Name $ Right (id, text)) <$> n
          ty' <- mapM (resolve vars) ty
          pure $ (label, OptBind (n', ty'))
    Ctr rn label -> pure $ Ctrχ rn label
    Rec rn (OptBind (n, a)) val cases -> do
      id <- fresh_id 
      let n' = (\text -> Name $ Right (id, text)) <$> n
          vars' = maybe vars (\t -> insert t (Left id) vars) n
      a' <- mapM (resolve vars) a 
      val' <- resolve vars val 
      cases' <- mapM (resolve_case vars') cases
      pure $ Recχ rn (OptBind (n', a')) val' cases'
      where 
        resolve_case vars (pat, val) = do
          (pat', vars') <- update_pat vars pat
          (pat', ) <$> resolve vars' val

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

    where
      resolve_tel vars [] = pure (vars, [])
      resolve_tel vars ((OptBind (t, a), val) : tel) = do
        id <- fresh_id 
        let n = (\text -> Name $ Right (id, text)) <$> t
            vars' = maybe vars (\t -> insert t (Left id) vars) t
        a' <- mapM (resolve vars) a 
        val' <- resolve vars' val 
        (vars'', tel') <- resolve_tel vars' tel
        pure $ (vars'', ((OptBind (n, a'), val') : tel'))


resolve_entry :: MonadGen m => Path Text -> Map Text (Either Integer QualName) -> ParsedEntry -> m ResolvedEntry
resolve_entry path vars entry = case entry of
  Singleχ rn (OptBind (t,a)) val -> do
    let qn = (path <>) . (:| []) <$> t
        n = Name . Left <$> qn
        vars' = case (t, qn) of
          (Just tx, Just nm) -> insert tx (Right nm) vars
          _ -> vars
    a' <- mapM (resolve vars) a
    val' <- resolve vars' val
    pure $ Singleχ rn (OptBind (n, a')) val'

  Mutualχ rn terms -> do
    (vars', binds) <- resolve_types vars terms
    terms' <- mapM (\((_,val,_),(n',type')) -> do
                       val' <- resolve vars' val
                       pure (n', val', type'))
                     (zip terms binds)
    
    pure $ Mutualχ rn terms'
    where 
      resolve_types :: MonadGen m => Map Text (Either Integer QualName) -> [(Text, ParsedCore, ParsedCore)] -> m (Map Text (Either Integer QualName), [(Name, ResolvedCore)])
      resolve_types vars ((n, t, _) : ts) = do
        id <- fresh_id
        let n' = Name $ Right (id, n)
            vars' = insert n (Left id) vars
        t' <- resolve vars t
        (vars', binds') <- resolve_types vars' ts
        pure (vars', (n',t') : binds')
      resolve_types vars [] = pure (vars, [])

-- TODO: interface with environment somehow? (based on imports/exports)

resolve_module :: MonadGen m => Path Text -> Map Text (Either Integer QualName) -> ParsedModule -> m ResolvedModule
resolve_module path vars modul = do
  entries' <- resolve_entries vars (modul^.module_entries)
  pure $ (module_entries .~ entries') modul

  where 
    resolve_entries :: MonadGen m => Map Text (Either Integer QualName) -> [ParsedEntry] -> m [ResolvedEntry]
    resolve_entries _ [] = pure []
    resolve_entries vars (e:es) = do
      e' <- resolve_entry path vars e
      let vars' = update_vars vars e'
      (e' :) <$> resolve_entries vars' es 

    update_vars vars entry = case entry of 
      Singleχ _ (OptBind (n,_)) _ -> do
        maybe vars (\(nm, txt) -> insert txt nm vars) (get_local_name <$> n)
      Mutualχ _ mutuals -> do
        foldl' (\vars (n,_,_) -> (\(nm,text) -> insert text nm vars) (get_local_name n)) vars mutuals
        --maybe vars (\(id,text) -> Map.insert n id vars) ((,) <$> get_id n <*> get_text n)

    get_local_name (Name (Right (id, text))) = (Left id, text)
    get_local_name (Name (Left p)) = (Right p, NonEmpty.last p)
