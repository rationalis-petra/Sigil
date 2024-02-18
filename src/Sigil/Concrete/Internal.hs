module Sigil.Concrete.Internal
  ( Internal
  , InternalTel
  , InternalCore
  , InternalFormula
  , InternalEntry
  , InternalModule
  , InternalPackage
  , Pattern(..)
  , pattern Uni
  , pattern Var
  , pattern Prd
  , pattern Abs
  , pattern App
  , pattern Ind
  , pattern Ctr
  , pattern Rec
  , pattern Eql
  , pattern Dap
  , pattern TrL
  , pattern TrR
  ) where

import Data.Functor.Identity
import Data.Text (Text)
import Prettyprinter

import Sigil.Abstract.Names
import Sigil.Abstract.Syntax
import Sigil.Abstract.Unify (Formula)
import Sigil.Concrete.Decorations.Implicit
import Sigil.Concrete.Decorations.Range

data Internal

type instance Functorχ Internal = Identity
type instance Coreχ AnnBind Name Internal = ()
type instance Varχ Internal = ()
type instance Uniχ Internal = ()
type instance Prdχ Internal = ArgType
type instance Absχ Internal = ArgType
type instance Appχ Internal = ArgType
type instance Indχ Internal = ()
type instance Ctrχ Internal = ()
type instance Recχ Internal = ()
type instance Eqlχ Internal = ()
type instance Dapχ Internal = ()
type instance TrLχ Internal = ()
type instance TrRχ Internal = ()

type instance Singleχ Internal = ()

type InternalCore = Core AnnBind Name Internal
  
type InternalFormula = Formula Name (Core AnnBind Name Internal)

type InternalTel = Tel AnnBind Name InternalCore

type InternalEntry = Entry AnnBind Name Internal

type InternalModule = Module AnnBind Name Internal  

type InternalPackage = Package InternalModule

{-# COMPLETE Uni, Var, Prd, Abs, App, Ind, Ctr, Rec, Eql, Dap, TrL, TrR #-}

pattern Uni :: Integer -> InternalCore
pattern Uni n <- Uniχ () n
  where Uni n = Uniχ () n

pattern Var :: Name -> InternalCore
pattern Var n <- Varχ () n 
  where Var n = Varχ () n

pattern Prd :: ArgType -> AnnBind Name InternalCore -> InternalCore -> InternalCore
pattern Prd at b ty <- Prdχ at b ty 
  where Prd at b ty = Prdχ at b ty

pattern Abs :: ArgType -> AnnBind Name InternalCore -> InternalCore -> InternalCore
pattern Abs at b e <- Absχ at b e 
  where Abs at b e = Absχ at b e

pattern App :: ArgType -> InternalCore -> InternalCore -> InternalCore
pattern App at l r <- Appχ at l r
  where App at l r = Appχ at l r

pattern Ind :: Name -> InternalCore -> [(Text, InternalCore)] -> InternalCore
pattern Ind name sort ctors <- Indχ () name (Identity sort) ctors
  where Ind name sort ctors = Indχ () name (Identity sort) ctors

pattern Ctr :: Text -> InternalCore -> InternalCore
pattern Ctr label ty <- Ctrχ () label (Identity ty)
  where Ctr label ty = Ctrχ () label (Identity ty)

pattern Rec :: AnnBind Name InternalCore -> InternalCore -> [(Pattern Name, InternalCore)] -> InternalCore
pattern Rec bind val cases <- Recχ () bind val cases
  where Rec bind val cases = Recχ () bind val cases

pattern Eql :: [(AnnBind Name (InternalCore, InternalCore, InternalCore), InternalCore)] -> InternalCore -> InternalCore -> InternalCore -> InternalCore
pattern Eql tel ty a a' <- Eqlχ () tel ty a a'
  where Eql tel ty a a' = Eqlχ () tel ty a a'

pattern Dap :: [(AnnBind Name (InternalCore, InternalCore, InternalCore), InternalCore)] -> InternalCore -> InternalCore
pattern Dap tel val <- Dapχ () tel val
  where Dap tel val = Dapχ () tel val

pattern TrL :: [(AnnBind Name (InternalCore, InternalCore, InternalCore), InternalCore)] -> InternalCore -> InternalCore -> InternalCore
pattern TrL tel ty val <- TrLχ () tel ty val
  where TrL tel ty val = TrLχ () tel ty val

pattern TrR :: [(AnnBind Name (InternalCore, InternalCore, InternalCore), InternalCore)] -> InternalCore -> InternalCore -> InternalCore
pattern TrR tel ty val <- TrRχ () tel ty val
  where TrR tel ty val = TrRχ () tel ty val


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

    Prd _ _ _ -> pretty_prd_like c
  
    Abs _ _ _ -> pretty_abs_like c

    App at l r -> sep $ unwind (App at l r)

    Ind name sort ctors -> vsep
      [ "μ" <+> pretty name <+> "⮜" <+> pretty sort <> "."
      , indent 2 (align (vsep (map (\(l,ty) -> pretty l <+> "⮜" <+> pretty ty) ctors)))
      ]

    Ctr label _  -> ":" <> pretty label

    Rec recur val cases -> vsep
      [ "φ" <+> pretty_annbind Regular True recur <> "," <+> pretty val <> "."
      , indent 2 (align (vsep (map (\(pat, val) -> pretty_pat pat <+> "→" <+> pretty val) cases)))
      ]
      where 
        pretty_pat = \case
          (PatCtr n pats) -> pretty (":" <> n) <+> sep (map pretty_pat pats)
          (PatVar n) -> pretty n
    Eql tel ty a b -> ("ι" <+> pretty_tel tel <+> "." <+> bracket ty <+> bracket a <+> bracket b)

    Dap tel val -> ("ρ" <+> pretty_tel tel <+> "." <+> pretty val)
    TrL tel ty val -> ("⍃" <+> pretty_tel tel <+> "." <+> pretty ty <+> pretty val)
    TrR tel ty val -> ("⍄" <+> pretty_tel tel <+> "." <+> pretty ty <+> pretty val)


    where 
      pretty_prd_like e =
        align $ sep $ head tel : map ("→" <+>) (tail tel)
        where
          tel = telescope e
        
          telescope (Prd at bind e) = (pretty_annbind at False bind) : telescope e
          telescope b = [pretty b]

      pretty_abs_like e =
        let (args, body) = telescope e
            telescope (Abs at bind e) =
              let (args, body) = telescope e in 
                ((at , bind) : args, body)
            telescope body = ([], body)
    
            pretty_args [(at, bind)] = pretty_annbind at True bind
            pretty_args ((at, bind) : xs) = pretty_annbind at True bind <+> pretty_args xs
            pretty_args [] = mempty
        in
          ("λ" <+> pretty_args args <+> "→") <+> nest 2 (bracket body)

      pretty_annbind at fnc bind =
        let lp = if at == Regular then "(" else "⟨"
            rp = if at == Regular then ")" else "⟩"
        in case bind of 
          AnnBind (Name (Right (_, "_")), ty) ->
            if fnc
            then lp <>"_⮜" <> pretty ty <> rp
            else bracket ty
          AnnBind (n, ty) -> lp <> pretty n <+> "⮜" <+> pretty ty <> rp

      pretty_tel [] = ""
      pretty_tel [(bind, val)] = pretty_eq_bind bind <+> pretty val
      pretty_tel ((bind, val) : tel) =
        pretty_eq_bind bind <+> pretty val <+> "," <+> pretty_tel tel

      pretty_eq_bind (AnnBind (nm, (ty, v1, v2))) = 
        pretty nm <+> "⮜" <+> pretty ty <+> ("(" <> pretty v1 <+> "=" <+> pretty v2 <> ")")

      bracket v = if iscore v then pretty v else "(" <> pretty v <> ")"
      
      iscore (Uni _) = True
      iscore (Var _) = True
      iscore (Ctr _ _) = True
      iscore _ = False

      unwind (App at l r) = unwind l <> case at of
        Regular -> [bracket r]
        Implicit -> ["⟨" <> pretty r <> "⟩"]
      unwind t = [bracket t]
  

instance Pretty InternalEntry where
  pretty = pretty_entry_builder name pretty pretty pretty

instance Pretty InternalModule where
  pretty = pretty_mod_builder pretty

instance HasRange InternalCore where
  range _ = Range Nothing
