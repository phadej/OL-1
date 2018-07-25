module OL1.Check (infer, check) where

import Bound.ScopeH
import Bound.Var     (Var (..))
import Control.Monad (unless)

import OL1.Error
import OL1.Expr
import OL1.Name
import OL1.Pretty
import OL1.Type

-- | Infer 'Inf b' type.
infer
    :: (Eq b, Pretty a, Pretty b)
    => (a -> Maybe (Poly b))
    -> Inf b a
    -> Either Err (Poly b)
infer = rinfer []

-- | Check 'Chk b' type.
check
    :: (Eq b, Pretty a, Pretty b)
    => (a -> Maybe (Poly b))
    -> Chk b a
    -> Poly b
    -> Either Err ()
check = rcheck []

-------------------------------------------------------------------------------
-- Implementation
-------------------------------------------------------------------------------

rinfer
    :: (Eq b, Pretty a, Pretty b)
    => [Doc]
    -> (a -> Maybe (Poly b))
    -> Inf b a
    -> Either Err (Poly b)
rinfer ts ctx term = case term of
    V x -> case ctx x of
        Nothing -> Left $ VariableNotInScope (ppr x) ts
        Just t  -> pure t
    Ann x t -> do
        rcheck ts' ctx x t
        pure t
    App f x -> do
        ft <- rinfer ts' ctx f
        case ft of
            Mono (a :-> b) -> do
                rcheck ts' ctx x (Mono a)
                pure (Mono b)
            _ -> Left $ NotAFunction (ppr ft) (ppr f) (ppr x) ts'
    AppTy x t -> do
        xt <- rinfer ts' ctx x
        case xt of
            Forall _ b -> pure $ instantiate1H t b
            _          -> Left $ NotAPolyFunction (ppr xt) (ppr x) (ppr t) ts'
  where
    ts' = ppr term : ts

rcheck
    :: (Eq b, Pretty a, Pretty b)
    => [Doc] -- ^ terms we walked through, for error reporting
    -> (a -> Maybe (Poly b))
    -> Chk b a
    -> Poly b
    -> Either Err ()
rcheck ts ctx term t = case term of
    Inf u -> do
        t' <- rinfer ts' ctx u
        unless (t == t') $ Left $ TypeMismatch (ppr t) (ppr t') (ppr u) ts
    Lam _n e -> case t of
        Mono (a :-> b) -> do
            let e' = fromScopeH e
            rcheck ts' (addContext a ctx) e' (Mono b)
        _ -> Left $ LambdaNotArrow (ppr t) (ppr term) ts
    LamTy _n e ->  case t of
        Forall _m s -> do
            let e' = unChk' $ fromScopeH e
            let s' = fromScopeH s
            rcheck ts' (fmap (fmap F) . ctx) e' s'
        _ -> Left $ PolyNotForall (ppr t) (ppr term) ts
  where
    ts' = ppr term : ts

addContext
    :: Mono b                  -- ^ x
    -> (a -> Maybe (Poly b))   -- ^ context
    -> Var N a
    -> Maybe (Poly b)
addContext x _ (B _) = Just (Mono x)
addContext _ f (F x) = f x
