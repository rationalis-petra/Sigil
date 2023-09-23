module Sigil.Analysis.NameResolution
  ( ResolveTo(..)
  , resolve_closed
  ) where


import Prelude hiding (lookup)
import Control.Lens
import Data.Map (Map, lookup, insert, empty)
import Data.Text (Text)
import Data.Foldable (foldl')

import Sigil.Abstract.Syntax
import Sigil.Abstract.Environment hiding (Environment(..)) 

import Sigil.Concrete.Parsed
import Sigil.Concrete.Resolved


{------------------------------- ID GENERATION ---------------------------------}
{-                                                                             -}
{-                                                                             -}
{-                                                                             -}
{-------------------------------------------------------------------------------}

class ResolveTo a b | a -> b where
  resolve :: MonadGen m => Map Text Integer -> a -> m b

resolve_closed :: (MonadGen m, ResolveTo a b) => a -> m b
resolve_closed = resolve empty

instance ResolveTo ParsedCore ResolvedCore where
  resolve vars term = case term of 
    Core -> pure $ Coreχ ()
    Uni rn n -> pure $ Uniχ rn n
    Var rn name -> case lookup name vars of
      Just n -> pure $ Varχ rn $ Name $ Right (n, name)
      Nothing -> pure $ Varχ rn $ Name $ Left [name]
    Prd rn (OptBind (t, a)) ty -> do
      id <- fresh_id
      let n = (\text -> Name $ Right (id,text)) <$> t
          vars' = maybe vars (\t -> insert t id vars) t
      a' <- mapM (resolve vars) a
      Prdχ rn (OptBind (n, a')) <$> resolve vars' ty
    Abs rn (OptBind (t, ty)) e -> do
      id <- fresh_id
      let
        n = (\text -> Name $ Right (id,text)) <$> t 
        vars' = maybe vars (\t -> insert t id vars) t
      ty' <- mapM (resolve vars) ty
      Absχ rn (OptBind (n, ty')) <$> resolve vars' e
    App rn l r -> Appχ rn <$> resolve vars l <*> resolve vars r
    Eql rn tel ty a a' -> do
      (vars', tel') <- resolve_tel vars tel
      Eqlχ rn tel' <$> resolve vars' ty <*> resolve vars' a <*> resolve vars' a'
    Dap rn tel val -> do
      (vars', tel') <- resolve_tel vars tel
      Dapχ rn tel' <$> resolve vars' val
    where
      resolve_tel vars [] = pure (vars, [])
      resolve_tel vars ((OptBind (t, a), val) : tel) = do
        id <- fresh_id 
        let n = (\text -> Name $ Right (id, text)) <$> t
            vars' = maybe vars (\t -> insert t id vars) t
        a' <- mapM (resolve vars) a 
        val' <- resolve vars' val 
        (vars'', tel') <- resolve_tel vars' tel
        pure $ (vars'', ((OptBind (n, a'), val') : tel'))


instance ResolveTo ParsedEntry ResolvedEntry where
  resolve vars entry = case entry of
    Singleχ rn (OptBind (t,a)) val -> do
      id <- fresh_id 
      let n = Name . Right . (id,) <$> t
          vars' = maybe vars (\t -> insert t id vars) t
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
        resolve_types :: MonadGen m => Map Text Integer -> [(Text, ParsedCore, ParsedCore)] -> m (Map Text Integer, [(Name, ResolvedCore)])
        resolve_types vars ((n, t, _) : ts) = do
          id <- fresh_id
          let n' = Name $ Right (id, n)
              vars' = insert n id vars
          t' <- resolve vars t
          (vars', binds') <- resolve_types vars' ts
          pure (vars', (n',t') : binds')
        resolve_types vars [] = pure (vars, [])

instance ResolveTo ParsedModule ResolvedModule where
  -- TODO: interface with environment somehow? (based on imports/exports)
  resolve vars modul = do
    entries' <- resolve_entries vars (modul^.module_entries)
    pure $ (module_entries .~ entries') modul

    where 
      resolve_entries :: MonadGen m => Map Text Integer -> [ParsedEntry] -> m [ResolvedEntry]
      resolve_entries _ [] = pure []
      resolve_entries vars (e:es) = do
        e' <- resolve vars e
        let vars' = update_vars vars e'
        (e' :) <$> resolve_entries vars' es 

      update_vars vars entry = case entry of 
        Singleχ _ (OptBind (n,_)) _ -> do
          maybe vars (\(id, text) -> insert text id vars) (get_local_name =<< n)
        Mutualχ _ mutuals -> do
          foldl' (\vars (n,_,_) -> maybe vars (\(id,text) -> insert text id vars) (get_local_name n)) vars mutuals
          --maybe vars (\(id,text) -> Map.insert n id vars) ((,) <$> get_id n <*> get_text n)

      get_local_name (Name (Right p)) = Just p
      get_local_name _ = Nothing
