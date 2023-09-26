module Sigil.Concrete.Internal
  ( Internal
  , InternalCore
  , InternalEntry
  , InternalModule
  , pattern Uni
  , pattern Var
  , pattern Prd
  , pattern Abs
  , pattern App
  , pattern Eql
  , pattern Dap
  , pattern IAbs
  , pattern IPrd
  , pattern TyCon ) where

import Prettyprinter

import Sigil.Abstract.Environment
import Sigil.Abstract.Syntax
import Sigil.Concrete.Decorations.Implicit
import Sigil.Concrete.Decorations.Range

data Internal

type instance Coreχ AnnBind Name Internal = ImplCore AnnBind Name Internal
type instance Varχ Internal = ()
type instance Uniχ Internal = ()
type instance Prdχ Internal = ()
type instance Absχ Internal = ()
type instance Appχ Internal = ()
type instance Eqlχ Internal = ()
type instance Dapχ Internal = ()
type instance IAbsχ Internal = ()
type instance IPrdχ Internal = ()
type instance TyConχ Internal = ()

type instance Singleχ Internal = ()
type instance Mutualχ Internal = ()

type InternalCore = Core AnnBind Name Internal

type instance Mutualχ Internal = ()

type InternalEntry = Entry AnnBind Name Internal

type InternalModule = Module AnnBind Name Internal  

{-# COMPLETE Uni, Var, Prd, Abs, App, Eql, Dap, IPrd, IAbs, TyCon #-}

pattern Uni :: Integer -> InternalCore
pattern Uni n <- Uniχ () n
  where Uni n = Uniχ () n

pattern Var :: Name -> InternalCore
pattern Var n <- Varχ () n 
  where Var n = Varχ () n

pattern Prd :: AnnBind Name InternalCore -> InternalCore -> InternalCore
pattern Prd b ty <- Prdχ () b ty 
  where Prd b ty = Prdχ () b ty

pattern Abs :: AnnBind Name InternalCore -> InternalCore -> InternalCore
pattern Abs b e <- Absχ () b e 
  where Abs b e = Absχ () b e

pattern App :: InternalCore -> InternalCore -> InternalCore
pattern App l r <- Appχ () l r
  where App l r = Appχ () l r

pattern Eql :: [(AnnBind Name (InternalCore, InternalCore, InternalCore), InternalCore)] -> InternalCore -> InternalCore -> InternalCore -> InternalCore
pattern Eql tel ty a a' <- Eqlχ () tel ty a a'
  where Eql tel ty a a' = Eqlχ () tel ty a a'

pattern Dap :: [(AnnBind Name (InternalCore, InternalCore, InternalCore), InternalCore)] -> InternalCore -> InternalCore
pattern Dap tel val <- Dapχ () tel val
  where Dap tel val = Dapχ () tel val

pattern IPrd :: AnnBind Name InternalCore -> InternalCore -> InternalCore
pattern IPrd b ty <- Coreχ (IPrdχ () b ty)
  where IPrd b ty = Coreχ (IPrdχ () b ty)

pattern IAbs :: AnnBind Name InternalCore -> InternalCore -> InternalCore
pattern IAbs b ty <- Coreχ (IAbsχ () b ty)
  where IAbs b ty = Coreχ (IAbsχ () b ty)

pattern TyCon :: Name -> InternalCore -> InternalCore
pattern TyCon n e <- Coreχ (TyConχ () n e)  
  where TyCon n e = Coreχ (TyConχ () n e)


instance Pretty InternalCore where
  pretty c = case c of  
    Uni n -> "𝕌" <> pretty_subscript n
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
    Var name -> pretty name

 
    Prd _ _ -> pretty_prd_like c
    IPrd _ _ -> pretty_prd_like c
  
    Abs _ _ -> pretty_abs_like c
    IAbs _ _ -> pretty_abs_like c

    App l r -> sep $ fmap bracket $ unwind (App l r)

    Eql tel ty a b -> ("ι" <+> pretty_tel tel <+> pretty ty <+> pretty a <+> pretty b)
    Dap tel val -> ("ρ" <+> pretty_tel tel <+> pretty val)

    TyCon _ _ -> "tycon"
  
    where 
      pretty_prd_like e =
        align $ sep $ head tel : map ("→" <+>) (tail tel)
        where
          tel = telescope e
        
          telescope (Prd bind e) =  pretty_annbind False bind : telescope e
          telescope (IPrd bind e) = ("{" <> pretty_annbind False bind <> "}") : telescope e
          telescope b = [pretty b]

      pretty_abs_like e =
        let (args, body) = telescope e
            telescope (Abs bind e) =
              let (args, body) = telescope e in 
                ((False, bind) : args, body)
            telescope (IAbs bind e) =
              let (args, body) = telescope e in
                ((True, bind) : args, body)
            telescope body = ([], body)
    
            pretty_args [(False, bind)] =
              pretty_annbind True bind
            pretty_args [(True, bind)] =
              ("{" <> pretty_annbind True bind <> "}")
            pretty_args ((False, bind) : xs) =
              pretty_annbind True bind <+> pretty_args xs
            pretty_args ((True, bind) : xs) =
              ("{" <> pretty_annbind True bind <> "}") <+> pretty_args xs
            pretty_args [] = mempty
        in
          ("λ" <+> pretty_args args <+> "→") <+> nest 2 (bracket body)

      pretty_annbind fnc = \case
        AnnBind (Name (Right (_, "_")), ty) ->
          if fnc
          then "(_⮜" <> pretty ty <> ")"
          else bracket ty
        AnnBind (n, ty) -> "(" <> pretty n <+> "⮜" <+> pretty ty <> ")"

      pretty_tel [] = "."
      pretty_tel [(bind, val)] = pretty_eq_bind bind <+> "." <+> pretty val
      pretty_tel ((bind, val) : tel) =
        pretty_eq_bind bind <+> "." <+> pretty val <+> "," <+> pretty_tel tel

      pretty_eq_bind (AnnBind (nm, (ty, v1, v2))) = 
        pretty nm <+> "⮜" <+> pretty ty <+> ("(" <> pretty v1 <+> "=" <+> pretty v2 <> ")")

      bracket v = if iscore v then pretty v else "(" <> pretty v <> ")"
      
      iscore (Uni _) = True
      iscore (Var _) = True
      iscore _ = False

      unwind (App l r) = unwind l <> [r]
      unwind t = [t]

instance Pretty (ImplCore AnnBind Name Internal) where
  pretty ic = case ic of 
    IAbsχ _ b body -> "λ ⟨" <> pretty_bind True b <> "⟩" <+> "→" <+> pretty body
    IPrdχ _ b body -> "⟨" <> pretty b <> "⟩" <+> "→" <+> pretty body
    TyConχ _ n body -> "[" <> pretty n <+> "<:" <+> pretty body <> "]"   -- Constrains named type n  

instance Pretty InternalEntry where
  pretty = pretty_entry_builder name pretty pretty pretty

instance Pretty InternalModule where
  pretty = pretty_mod_builder pretty

instance HasRange InternalCore where
  range _ = Range Nothing
