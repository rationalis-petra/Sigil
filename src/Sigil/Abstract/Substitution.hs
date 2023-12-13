{-# OPTIONS_GHC -XDeriveTraversable #-}
module Sigil.Abstract.Substitution
  ( Substitution
  , Subst(..)
  , subst
  , insert
  , lookup
  , empty
  , (↦)
  , Regen(..) ) where


{-------------------------------- SUBSTITUTION ---------------------------------}
{- This module contains the Subst typeclass, which supports two kinds of       -}
{- substitution:                                                               -}
{- 1. Regular, unnormalizing substitution.                                     -}
{- 2. Typed, hereditary substitution.                                          -}
{-                                                                             -}
{-------------------------------------------------------------------------------}


import Prelude hiding (lookup)
import Data.Foldable 
import Data.Maybe (fromMaybe)
import qualified Data.Set as Set
import Data.Set (Set)
import qualified Data.Map as Map
import Data.Map (Map)

import Prettyprinter

import Sigil.Abstract.Syntax
import Sigil.Abstract.Names


newtype Substitution n a = Substitution (Map n a)
  deriving (Functor, Foldable, Traversable)

instance (Pretty n, Pretty a) => Pretty (Substitution n a) where
  pretty (Substitution subst) = vsep $ fmap (\(n,a) -> pretty n <+> "↦" <+> pretty a) $ Map.toList subst

class Subst n s a | a -> s n where
  substitute :: Set n -> Substitution n s -> a -> a
  free_vars :: a -> Set n
  
class Regen a where  
  regen :: MonadGen m => a -> m a
  
subst :: (Subst n s a) => Substitution n s -> a -> a
subst = substitute Set.empty

empty :: Substitution n a
empty = Substitution Map.empty

lookup :: (Ord n) => n -> Substitution n a -> Maybe a
lookup var (Substitution m) = Map.lookup var m

insert :: (Ord n) => n -> a -> Substitution n a -> Substitution n a
insert var val (Substitution m) = Substitution $ Map.insert var val m

(↦) :: (Ord n) => n -> a -> Substitution n a
n ↦ v = insert n v empty

instance (Ord n, Subst n a a) => Semigroup (Substitution n a) where
  (Substitution m1) <> (Substitution m2) =
    Substitution $ Map.union m2 $ fmap (subst (Substitution m2)) m1

instance (Ord n, Subst n a a) => Monoid (Substitution n a) where
  mempty = empty


{--------------------------- SUBSTITUTION INSTANCES ----------------------------}
{-                                                                             -}
{-                                                                             -}
{-                                                                             -}
{-------------------------------------------------------------------------------}

instance (Ord n, Subst n s a) => Subst n s (a, a, a) where 
  substitute shadow sub (x, y, z) = 
    ( substitute shadow sub x
    , substitute shadow sub y
    , substitute shadow sub z
    )

  free_vars (x, y, z) = free_vars x <> free_vars y <> free_vars z

instance (Ord n, Subst n s a) => Subst n s [a] where 
  substitute shadow sub = fmap (substitute shadow sub)

  free_vars = foldl' Set.union Set.empty . fmap free_vars  

instance (Ord n, Subst n s a) => Subst n s (OptBind n a) where
  substitute shadow sub (OptBind (n, ty)) = substitute shadow' sub (OptBind (n, ty'))
    where
      shadow' = maybe shadow (flip Set.insert shadow) n
      ty' = fmap (substitute shadow' sub) ty 

  free_vars (OptBind (n, ty)) =
    maybe id Set.delete n $ fromMaybe Set.empty (free_vars <$> ty)
  
instance (Ord n, Subst n s a) => Subst n s (AnnBind n a) where
  substitute shadow sub (AnnBind (n, a)) = AnnBind (n, substitute shadow'  sub a)
    where
      -- shadow' = maybe shadow (flip Set.insert shadow) n
      shadow' = Set.insert n shadow

  free_vars (AnnBind (n, a)) = Set.delete n $ free_vars a
    --maybe id Set.delete n $ free_vars a

instance ( Ord n
         , Binding b
         , Traversable (Functorχ χ)
         , Subst n (Core b n χ) (b n (Core b n χ))
         , Subst n (Core b n χ) (b n (Core b n χ, Core b n χ, Core b n χ)))
          => Subst n (Core b n χ) (Core b n χ) where 
  substitute shadow sub term = case term of
    Coreχ χ -> Coreχ χ 
    Uniχ χ n -> Uniχ χ n
    Varχ _ var ->
      if Set.member var shadow then
        term
      else
        fromMaybe term (lookup var sub)
    Prdχ χ bind ty ->
      Prdχ χ (substitute shadow sub bind) (substitute shadow' sub ty)
      where
        shadow' = maybe shadow (\n -> Set.insert n shadow) (name bind)
    Absχ χ bind body ->
      Absχ χ (substitute shadow sub bind) (substitute shadow' sub body)
      where
        shadow' = maybe shadow (\n -> Set.insert n shadow) (name bind)
    Appχ χ l r -> Appχ χ (substitute shadow sub l) (substitute shadow sub r)

    Eqlχ χ tel ty a a' ->
      Eqlχ χ tel'
        (substitute shadow' sub ty)
        (substitute shadow' sub a)
        (substitute shadow' sub a')
        where 
          (tel', shadow') = subst_tel shadow sub tel

    Dapχ χ tel val ->
      Dapχ χ tel' (substitute shadow' sub val)
       where
         (tel', shadow') = subst_tel shadow sub tel

    Indχ χ name fsort terms ->
      Indχ χ name (substitute shadow sub <$> fsort) (map subst_term terms)
      where 
        subst_term (text, val) = (text, substitute shadow' sub val)
        shadow' = Set.insert name shadow
    Ctrχ χ label ty -> Ctrχ χ label (substitute shadow sub <$> ty)

    Recχ χ recur val cases ->
      Recχ χ
        (substitute shadow sub recur)
        (substitute shadow' sub val)
        (map subst_case cases)
      where 
        shadow' = maybe shadow (\n -> Set.insert n shadow) (name recur)
        subst_case (pat, body) = (pat, substitute (shadow <> pat_shadow pat) sub body)
        pat_shadow = \case
          PatVar n -> Set.singleton n
          PatCtr _ subpats -> fold (map pat_shadow subpats)

    where
      subst_tel shadow _ [] = ([], shadow)
      subst_tel shadow sub ((bind, ty) : tel) =
        (((substitute shadow sub bind , substitute shadow' sub ty) : tel'), shadow'')
        where
          shadow' = maybe shadow (\n -> Set.insert n shadow) (name bind)
          (tel', shadow'') = subst_tel shadow' sub tel

  free_vars term = case term of 
    Coreχ _ -> Set.empty
    Uniχ _ _ -> Set.empty
    Varχ _ var -> Set.singleton var
    Prdχ _ bind ty -> let fvt = free_vars ty in
      free_vars bind <> maybe fvt (\n -> Set.delete n fvt) (name bind)
    Absχ _ bind body -> let fvb = free_vars body in
      free_vars bind <> maybe fvb (\n -> Set.delete n fvb) (name bind)
    Appχ _ l r -> Set.union (free_vars l) (free_vars r)
    Eqlχ _ tel ty a a' -> 
      let (vars, diff_vars) = free_tel tel
      in vars <>
          Set.difference 
           (free_vars ty <> free_vars a <> free_vars a')
           diff_vars
    Dapχ _ tel val -> 
      let (vars, diff_vars) = free_tel tel
      in vars <> Set.difference (free_vars val) diff_vars
    Indχ _ name fsort terms ->
      let fvt = fold (map (free_vars . snd) terms)
      in Set.delete name fvt <> (fold . fmap free_vars) fsort
    Ctrχ _ _ ty -> foldl' (\s v -> s <> free_vars v) Set.empty ty
    Recχ _ recur val cases ->
      let fvc = fold . map free_case_vars $ cases
          free_case_vars (pat, term) = Set.difference (free_vars term) (pat_vars pat)
          pat_vars = \case 
            PatCtr _ subpats -> fold (map pat_vars subpats)
            PatVar n -> Set.singleton n
      in
        free_vars recur <> free_vars val <> maybe fvc (\n -> Set.delete n fvc) (name recur)
    where 
      free_tel [] = (Set.empty, Set.empty)
      free_tel ((bind, val) : tel) =
        let (vars, diff_vars) = free_tel tel
            fvv = free_vars val
        in (free_vars bind
            <> (maybe fvv (\n -> Set.delete n fvv) (name bind))
            <> vars,
            maybe diff_vars (flip Set.insert diff_vars) (name bind))


instance Traversable (Functorχ χ) => Regen (Core OptBind Name χ) where 
  regen = go empty where
    freshen_bind (OptBind (n, ty)) sub = do
      n' <- mapM freshen n
      let sub' = maybe sub (flip (uncurry insert) sub) ((,) <$> n <*> n')
      ty' <- mapM (go sub) ty
      pure (sub', OptBind (n', ty'))

    freshen_eq_bind (OptBind (n, eql)) sub = do
      n' <- mapM freshen n
      let sub' = maybe sub (flip (uncurry insert) sub) ((,) <$> n <*> n')
      eql' <- mapM (\(ty, v1, v2) -> (,,) <$> go sub ty <*> go sub v1 <*> go sub v2) eql
      pure (sub', OptBind (n', eql'))

    freshen_tel [] sub = pure (sub, [])
    freshen_tel ((bind, id) : tel) sub = do
      (sub', bind') <- freshen_eq_bind bind sub
      id' <- go sub' id
      (sub'', tel') <- freshen_tel tel sub'
      pure (sub'', ((bind', id') : tel'))

    go sub term = case term of 
      Coreχ χ -> pure $ Coreχ χ 
      Uniχ χ n -> pure $ Uniχ χ n
      Varχ χ var -> case lookup var sub of 
        Just n' -> pure $ Varχ χ n'
        Nothing -> pure term
      Prdχ χ bind ty -> do
        (sub', bind') <- freshen_bind bind sub
        Prdχ χ bind' <$> (go sub' ty)
      Absχ χ bind body -> do
        (sub', bind') <- freshen_bind bind sub
        Absχ χ bind' <$> (go sub' body)
      Appχ χ l r -> Appχ χ <$> go sub l <*> go sub r
      Eqlχ χ tel ty a a' -> do
        (sub', tel') <- freshen_tel tel sub
        Eqlχ χ tel' <$> go sub' ty <*> go sub' a <*> go sub' a'
      Dapχ χ tel val -> do
        (sub', tel') <- freshen_tel tel sub
        Dapχ χ tel' <$> go sub' val
      Indχ χ name fsort ctors -> do
        name' <- freshen name
        fsort' <- mapM (go sub) fsort
        let sub' = insert name name' sub
        ctors' <- mapM (\(label, ty) -> ((label, ) <$> go sub' ty)) ctors
        pure $ Indχ χ name' fsort' ctors'
      Ctrχ χ label ty -> Ctrχ χ label <$> mapM (go sub) ty
      Recχ χ recur val cases -> do
        (sub', bind') <- freshen_bind recur sub
        Recχ χ bind' <$> go sub' val <*> mapM (freshen_case sub') cases
        where 
          freshen_case sub (pat, val) = do
            (sub', pat') <- freshen_pat sub pat
            val' <- go sub' val 
            pure (pat', val')
          freshen_pat sub = \case
            PatCtr n subpats -> do
              (sub', subpats') <- foldr (\p m -> do
                        (sub', ps) <- m
                        (sub'', p') <- freshen_pat sub' p 
                        pure (sub'', p' : ps))
                  (pure (sub, []))
                  subpats
              pure (sub', PatCtr n subpats')
            PatVar n -> do
              n' <- freshen n
              pure (insert n n' sub, PatVar n')

instance Traversable (Functorχ χ) => Regen (Core AnnBind Name χ) where 
  regen = go empty where
    freshen_bind (AnnBind (n, ty)) sub = do
      n' <- freshen n
      let sub' = insert n n' sub
      ty' <- go sub' ty
      pure (sub', AnnBind (n', ty'))

    freshen_eq_bind (AnnBind (n, eql)) sub = do
      n' <- freshen n
      let sub' = insert n n' sub
      eql' <- (\(ty, v1, v2) -> (,,) <$> go sub ty <*> go sub v1 <*> go sub v2) eql
      pure (sub', AnnBind (n', eql'))

    freshen_tel [] sub = pure (sub, [])
    freshen_tel ((bind, id) : tel) sub = do
      (sub', bind') <- freshen_eq_bind bind sub
      id' <- go sub' id 
      (sub'', tel') <- freshen_tel tel sub'
      pure (sub'', ((bind', id') : tel'))

    go sub term = case term of 
      Coreχ χ -> pure $ Coreχ χ 
      Uniχ χ n -> pure $ Uniχ χ n
      Varχ χ var -> case lookup var sub of 
        Just n' -> pure $ Varχ χ n'
        Nothing -> pure term
      Prdχ χ bind ty -> do
        (sub', bind') <- freshen_bind bind sub
        Prdχ χ bind' <$> (go sub' ty)
      Absχ χ bind body -> do
        (sub', bind') <- freshen_bind bind sub
        Absχ χ bind' <$> (go sub' body)
      Appχ χ l r -> Appχ χ <$> (go sub l) <*> (go sub r)
      Eqlχ χ tel ty a a' -> do
        (sub', tel') <- freshen_tel tel sub
        Eqlχ χ tel' <$> go sub' ty <*> go sub' a <*> go sub' a'
      Dapχ χ tel val -> do
        (sub', tel') <- freshen_tel tel sub
        Dapχ χ tel' <$> go sub' val
      Indχ χ name fsort ctors -> do
        name' <- freshen name
        fsort' <- mapM (go sub) fsort
        let sub' = insert name name' sub
        ctors' <- mapM (\(t, ty) -> (t, ) <$> go sub' ty) ctors
        pure $ Indχ χ name' fsort' ctors'
      Ctrχ χ label ty -> Ctrχ χ label <$> mapM (go sub) ty
      Recχ χ recur val cases -> do
        (sub', bind') <- freshen_bind recur sub
        Recχ χ bind' <$> go sub' val <*> mapM (freshen_case sub') cases
        where 
          freshen_case sub (pat, val) = do
            (sub', pat') <- freshen_pat sub pat
            val' <- go sub' val 
            pure (pat', val')
          freshen_pat sub = \case
            PatCtr n subpats -> do
              (sub', subpats') <- foldr (\p m -> do
                        (sub', ps) <- m
                        (sub'', p') <- freshen_pat sub' p 
                        pure (sub'', p' : ps))
                  (pure (sub, []))
                  subpats
              pure (sub', PatCtr n subpats')
            PatVar n -> do
              n' <- freshen n
              pure (insert n n' sub, PatVar n')
