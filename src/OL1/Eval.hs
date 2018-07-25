module OL1.Eval (Eval (..)) where

import Bound.Scope.Simple (toScope)
import Bound.ScopeH       (ScopeH (..), fromScopeH)
import Data.Bifunctor     (first)

import OL1.Expr
import OL1.Value

-- | /Assumption/ @t@ is well-typed.
class Eval t where
    nf :: t b a -> Intro b a

instance Eval Inf where
    nf (V x)            = VCoerce (VVar x)
    nf (Ann x _)        = nf x
    nf (App f x)        = valueApp (nf f) (nf x)
    nf (AppTy x t)      = valueAppTy (nf x) t

instance Eval Chk where
    nf (Inf x)     = nf x
    nf (Lam n s)   = VLam n $ toScope $ nf $ fromScopeH s
    nf (LamTy n s) = VLamTy n $ ScopeH $ Intro' $ first (fmap return) $ nf $ unChk' $ fromScopeH s
