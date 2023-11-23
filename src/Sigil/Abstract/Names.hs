module Sigil.Abstract.Names
  ( UniqueName
  , Path(..)
  , QualName
  , Name(..)
  , name_text

  , Binding(..)
  , OptBind(..)
  , AnnBind(..)
  , pretty_bind

  -- Fresh Variable Generation
  , MonadGen(..)
  , fresh_var
  , fresh_varn
  , freshen
  , Gen
  , run_gen
  ) where


import Prelude hiding (head, lookup)
import Control.Monad.Trans.Class (lift)
import Control.Monad.Except (ExceptT)
import Control.Monad.State (State, StateT, runState, get, modify)
import Control.Monad.Reader (ReaderT)
  
import Data.Foldable (fold)
import qualified Data.List.NonEmpty as NonEmpty
import Data.List.NonEmpty (NonEmpty(..))
import Data.Text (Text, pack)

import Prettyprinter  

{------------------------------------ NAMES ------------------------------------}
{-                                                                             -}
{-                                                                             -}
{-------------------------------------------------------------------------------}

newtype Path = Path { unPath :: NonEmpty Text }
  deriving (Eq, Ord, Semigroup)

instance Pretty Path where
  pretty = fold . fmap pretty . NonEmpty.intersperse "." . unPath

instance Show Path where
  show = fold . fmap show . NonEmpty.intersperse "." . unPath
  
-- A name with a unique identifier 
type UniqueName = (Integer, Text)

-- A qualified name is one which depends on the value of a toplevel definition
type QualName = NonEmpty Text

-- data DBName = QDBName QualName | DeBruijn Int (Maybe Text)
newtype Name = Name (Either QualName UniqueName)
  deriving (Eq, Ord)

name_text :: Name -> Text
name_text (Name (Left (t :| ts))) = last (t : ts)
name_text (Name (Right (_, t))) = t

{------------------------------ BIND ABSTRACTION -------------------------------}
{- There are 3 variants of binding we can have:                                -}
{- + Name but no type, e.g. λ [x] x                                            -}
{- + Type but no name, e.g. ℤ → ℤ                                              -}
{- + Both Name and type, e.g. λ [x:ℤ] (x + 1) or (A:𝕌) → A → A                 -}
{- Specific binding types may encompass any subset of these three, and the     -}
{- typeclass abstraction should account for any possible subset.               -}
{- Hence, name and type return maybes, and the only way to construct a binding -}
{- requires both a name and a type.                                            -}
{-------------------------------------------------------------------------------}


class Binding b where 
  name :: b n a -> Maybe n
  tipe :: b n a -> Maybe a
  bind :: n -> a -> b n a

{----------------------------- CONCRETE BINDINGS -------------------------------}
-- Bindings: 
-- TODO: add bindings with optionally no name!

-- An annotated binding
newtype AnnBind n ty = AnnBind { unann :: (n, ty) }
  deriving Eq

-- Binding instance for AnnBind
instance Functor (AnnBind n) where
  fmap f (AnnBind (n, ty)) = AnnBind (n, f ty)

instance Foldable (AnnBind n) where
  foldr f z (AnnBind (_, ty)) = f ty z
  foldl f z (AnnBind (_, ty)) = f z ty

instance Traversable (AnnBind n) where
  traverse f (AnnBind (n, ty)) = (\r -> AnnBind (n, r)) <$> f ty

instance Binding AnnBind where
  name (AnnBind (n, _)) = Just n
  tipe (AnnBind (_, ty)) = Just ty
  bind n ty = AnnBind (n, ty)

-- An optionally annotated binding
newtype OptBind n ty = OptBind { unOpt :: (Maybe n, Maybe ty) }
  deriving Eq

instance Functor (OptBind n) where
  fmap f (OptBind (n, ty)) = OptBind (n, fmap f ty)

instance Binding OptBind where   
  name (OptBind (n, _)) = n
  tipe (OptBind (_, ty)) = ty
  bind n ty = OptBind (Just n, Just ty)


{--------------------------------- GENERATION ----------------------------------}
{-                                                                             -}
{-------------------------------------------------------------------------------}

  
class Monad m => MonadGen m where 
  fresh_id :: m Integer

newtype Gen a = Gen { ungen :: State Integer a }
  deriving (Functor, Applicative, Monad)

instance MonadGen Gen where 
  fresh_id = do
    id <- Gen get
    Gen (modify (+ 1))
    pure id

instance MonadGen m => MonadGen (ExceptT e m) where
  fresh_id = lift fresh_id

instance MonadGen m => MonadGen (StateT e m) where
  fresh_id = lift fresh_id

instance MonadGen m => MonadGen (ReaderT e m) where
  fresh_id = lift fresh_id

run_gen :: Gen a -> a
run_gen = fst . flip runState 0 . ungen

fresh_var :: MonadGen m => Text -> m Name
fresh_var s = fresh_id >>= pure . Name . Right . (, s)

fresh_varn :: MonadGen m => Text -> m Name
fresh_varn s = fresh_id >>= pure . Name . Right . (\n -> (n, s <> (pack . show) n))

freshen :: MonadGen m => Name -> m Name
freshen (Name (Right (_, s))) = fresh_var s
freshen q = pure q


{---------------------------------- INSTANCES ----------------------------------}
{-                                                                             -}
{-------------------------------------------------------------------------------}

instance (Pretty n, Pretty ty) => Pretty (OptBind n ty) where
  pretty bind = case bind of  
    OptBind (Just n, Nothing) -> pretty n
    OptBind (Just n, Just ty) -> pretty n <+> "⮜" <+> pretty ty
    OptBind (Nothing, Nothing) -> "_"
    OptBind (Nothing, Just ty) -> "_⮜" <> pretty ty

instance (Pretty n, Pretty ty) => Pretty (AnnBind n ty) where
  pretty bind = case bind of
    AnnBind (n, ty) -> pretty n <+> "⮜" <+> pretty ty

instance Pretty Name where 
  pretty (Name name) = case name of
    Left qname -> pretty qname -- TODO prettify
    Right (_, var) -> pretty var

pretty_bind :: (Pretty n, Pretty ty, Binding b) => Bool -> b n ty -> Doc ann
pretty_bind fnc b = case (name b, tipe b) of
  (Just n, Just ty) -> "(" <> pretty n <+> "⮜" <+> pretty ty <> ")"
  (Nothing, Nothing) -> "_"
  (Just n, Nothing) -> if fnc then pretty n else "(" <> pretty n <> "⮜_)"
  (Nothing, Just ty) -> if fnc then "(_⮜" <> pretty ty <> ")" else pretty ty
