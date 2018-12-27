module OL1.Check (infer, check) where

import Bound.Scope.Simple (toScope)
import Bound.ScopeH
import Bound.Var          (Var (..))

import OL1.Error
import OL1.Expr
import OL1.Pretty
import OL1.Type
import OL1.Value

-- | Infer 'Inf b' type.
infer
    :: (Eq b, Pretty a, Pretty b)
    => (a -> Maybe (Poly b))
    -> Inf b a
    -> Either Err (Intro b a, Poly b)
infer = rinfer []

-- | Check 'Chk b' type.
check
    :: (Eq b, Pretty a, Pretty b)
    => (a -> Maybe (Poly b))
    -> Chk b a
    -> Poly b
    -> Either Err (Intro b a)
check = rcheck []

-------------------------------------------------------------------------------
-- Implementation
-------------------------------------------------------------------------------

rinfer
    :: (Eq b, Pretty a, Pretty b)
    => [MDoc]
    -> (a -> Maybe (Poly b))
    -> Inf b a
    -> Either Err (Intro b a, Poly b)
rinfer ts ctx term = case term of
    V x -> case ctx x of
        Nothing -> Left $ VariableNotInScope (ppr x) ts
        Just t  -> pure (return x, t)
    Ann x t -> do
        x' <- rcheck ts' ctx x t
        pure (x', t)
    App f x -> do
        (f', ft) <- rinfer ts' ctx f
        case ft of
            Mono (a :-> b) -> do
                x' <- rcheck ts' ctx x (Mono a)
                pure (valueApp f' x', Mono b)
            _ -> Left $ NotAFunction (ppr ft) (ppr f) (ppr x) ts'
    AppTy x t -> do
        (x', xt) <- rinfer ts' ctx x
        case xt of
            Forall _ b -> pure $ (valueAppTy x' t, instantiate1H t b)
            _          -> Left $ NotAPolyFunction (ppr xt) (ppr x) (ppr t) ts'
  where
    ts' = ppr term : ts

rcheck
    :: (Eq b, Pretty a, Pretty b)
    => [MDoc] -- ^ terms we walked through, for error reporting
    -> (a -> Maybe (Poly b))
    -> Chk b a
    -> Poly b
    -> Either Err (Intro b a)
rcheck ts ctx term t = case term of
    Inf u -> do
        (u', t') <- rinfer ts' ctx u
        if (t == t')
        then return u'
        else Left $ TypeMismatch (ppr t) (ppr t') (ppr u) ts
    Lam n e -> case t of
        Mono (a :-> b) -> do
            let ee = fromScopeH e
            ee' <- rcheck ts' (addContext a ctx) ee (Mono b)
            let e' = toScope ee'
            return $ VLam n a e'

        _ -> Left $ LambdaNotArrow (ppr t) (ppr term) ts
    LamTy n e ->  case t of
        Forall _m s -> do
            let ee = unChk' $ fromScopeH e
            let ss = fromScopeH s
            ee' <- rcheck ts' (addTyContext ctx) ee ss
            let e' = toScope $ Intro' ee'
            return $ VLamTy n e'
        _ -> Left $ PolyNotForall (ppr t) (ppr term) ts
  where
    ts' = ppr term : ts

addContext
    :: Mono b                  -- ^ x
    -> (a -> Maybe (Poly b))   -- ^ context
    -> Var n a
    -> Maybe (Poly b)
addContext x _ (B _) = Just (Mono x)
addContext _ f (F x) = f x

addTyContext
    :: (a -> Maybe (Poly b))   -- ^ context
    -> a -> Maybe (Poly (Var n b))
addTyContext ctx a = fmap (fmap F) $ ctx a
