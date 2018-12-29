{-# LANGUAGE FlexibleContexts  #-}
{-# LANGUAGE OverloadedStrings #-}
module OL1.Synth where

import Bound.ScopeH
import Bound.Var                 (Var (..))
import Control.Monad.Error.Class (MonadError (..))
import Control.Monad.Module      (Module (..))
import Control.Monad.State
import Control.Monad.Trans.Class (lift)
import Control.Unification.Rigid
       (MetaVar (..), RigidVariable, UTerm (..), Unify, applyBindings,
       applyBindingsAll, freeVar, runUnify, unify, withRigid)
import Data.Bifoldable           (bifoldMap)
import Data.Bifunctor            (Bifunctor (..))
import Data.Bitraversable        (bitraverse)
import Data.Functor.Product      (Product (..))
import Data.List                 (nub)
import Data.Monoid               (Endo (..))
import Data.String               (fromString)
import Data.Traversable          (for)

import qualified Data.Map.Strict as Map
import qualified Data.Vec.Lazy   as V

import OL1.Error
import OL1.Expr
import OL1.Internal
import OL1.Syntax
import OL1.Type

-------------------------------------------------------------------------------
-- Type aliases
-------------------------------------------------------------------------------

type Unify' b v = Unify ISym Err (MonoF b) v
type U b v = UTerm (MonoF b) v

-------------------------------------------------------------------------------
-- Conversions
-------------------------------------------------------------------------------

toU :: Mono (U b v) -> U b v
toU (T a)     = a
toU (a :-> b) = UTerm (toU a :=> toU b)
toU (Tuple x) = UTerm (TupleF (map toU x))

-------------------------------------------------------------------------------
-- High-level interface
-------------------------------------------------------------------------------

synth
    :: forall a b. (Ord a, Eq b, ToSyntax a, ToSyntax b)
    => (a -> Maybe (Poly b))
    -> Inf (Maybe b) a
    -> Either Err (Inf b a, [Warning a])
synth ctx
    = fmap (\(x, t, ws) -> (generalise x t, ws))
    . runUnify
    . action
  where
    action
        :: Inf (Maybe b) a
        -> Unify' b MetaVar (Inf (U b MetaVar) a, Poly (U b MetaVar), [Warning a])
    action expr0 = do
        (expr1, freeVars) <- flip runStateT Map.empty $ do
            let freeA a = case ctx a of
                    Just ty -> pure (fmap (UTerm . TF) ty, a)
                    Nothing -> do
                        freeVars <- get
                        case Map.lookup a freeVars of
                            Just v -> pure (Mono (T (UVar v)), a)
                            Nothing -> do
                                v <- lift (freeVar)
                                put (Map.insert a v freeVars)
                                pure (Mono (T (UVar v)), a)
            let freeB (Just b) = pure (UTerm (TF b))
                freeB Nothing  = UVar <$> lift (freeVar)
            bitraverse freeB freeA expr0

        -- there is no expr2
        (expr3, ty) <- synInfer [] expr1
        Pair (Inf' expr4) ty' <- applyBindingsAll $ Pair (Inf' expr3) ty

        warnings <- for (Map.toList freeVars) $ \(a, v) ->
            NotInScope a . toSyntax' . flattenMonoDoc <$> applyBindings (UVar v)

        return (expr4, ty', warnings)

-------------------------------------------------------------------------------
-- Warning
-------------------------------------------------------------------------------

data Warning a = NotInScope a SyntaxI

-- instance Pretty a => Pretty (Warning a) where
--    toSyntax' (NotInScope a d) = sexpr (pprText "not-in-scope") [toSyntax' a, d]

-------------------------------------------------------------------------------
-- Generalise
-------------------------------------------------------------------------------

flattenMono :: U b v -> Mono (Either v b)
flattenMono (UVar v)           = T (Left v)
flattenMono (UTerm (TF x))     = T (Right x)
flattenMono (UTerm (a :=> b))  = flattenMono a :-> flattenMono b
flattenMono (UTerm (TupleF x)) = Tuple (map flattenMono x)

flattenMonoDoc :: ToSyntax b => U b v -> Mono (Either v SyntaxI)
flattenMonoDoc = fmap (fmap toSyntax') . flattenMono

flattenPoly :: Poly (U b v) -> Poly (Either v b)
flattenPoly t = t >>== flattenMono

flattenInf :: Inf (U b v) a -> Inf (Either v b) a
flattenInf = flip bindInfMono flattenMono

flattenChk :: Chk (U b v) a -> Chk (Either v b) a
flattenChk = flip bindChkMono flattenMono

generalise :: Inf (U b MetaVar) a -> Poly (U b MetaVar) -> Inf b a
generalise x0 t0
    = first fromRight'
    $ fst
    $ foldr f (x1, t1) vars
  where
    x1 = flattenInf x0
    t1 = flattenPoly t0

    vars = nub $ appEndo
        (foldMap sing t1 <> bifoldMap sing (const mempty) x1)
        []

    sing (Left mv) = Endo (mv :)
    sing (Right _) = mempty

    fromRight' :: Either MetaVar b -> b
    fromRight' (Right b) = b
    fromRight' (Left i)  = error $ "panic! Ungeneralised variable " ++ show i

    f :: MetaVar
      -> (Inf (Either MetaVar b) a, Poly (Either MetaVar b))
      -> (Inf (Either MetaVar b) a, Poly (Either MetaVar b))
    f v (x, t) = (Ann x' t', t')  where
        n :: ISym
        n = fromString "t"

        x' = LamTy n $ abstractH abst $ Chk' $ unAnn x

        t' = Forall n $ abstractH abst t

        abst (Left v')
            | v == v'   = Just n
            | otherwise = Nothing
        abst (Right _)  = Nothing

-------------------------------------------------------------------------------
-- Specialise
-------------------------------------------------------------------------------

-- TBW

-------------------------------------------------------------------------------
-- Inference
-------------------------------------------------------------------------------

-- TODO: make constraint type, collect them

wrap :: U b v -> Poly (U b v)
wrap = Mono . T

synInfer
    :: (RigidVariable ISym v, Eq b, ToSyntax a, ToSyntax b, ToSyntax v)
    => [SyntaxI]
    -> Inf (U b v) (Poly (U b v), a)  -- ^ terms with meta leaves
    -> Unify' b v (Inf (U b v) a, Poly (U b v))
synInfer ts term = case term of
    V (ty, a) -> pure (V a, ty)
    Ann x t   -> do
        (x', t') <- synCheck ts' x t
        pure (Ann x' t', t')
    App f x   -> do
        (f', ab) <- synInfer ts' f
        sysInferApp ts' f' ab x
    AppTy x t -> do
        (x', xt) <- synInfer ts' x
        case xt of
            Forall _ b -> pure (AppTy x' t, instantiate1H t b)
            _          -> throwError $ NotAPolyFunction (toSyntax' xt) (ppr' x) (toSyntax' t) ts'


  where
    ppr' term' = toSyntax' $ uncurry (\t x -> sthe (toSyntax t) (toSyntax x)) <$> term'
    pprTerm    = ppr' term
    ts'        = pprTerm : ts

sysInferApp
    :: (Eq b, RigidVariable ISym v, ToSyntax a, ToSyntax b, ToSyntax v)
    => [SyntaxI]
    -> Inf (U b v) a
    -> Poly (U b v)
    -> Chk (U b v) (Poly (U b v ), a)
    -> Unify' b v (Inf (U b v) a, Poly (U b v))
sysInferApp ts' f ab x = case ab of
    Mono (T ab') -> do
        a        <- UVar <$> freeVar
        (x', _)  <- synCheck ts' x (wrap a) -- TODO: synCheckMono
        b        <- UVar <$> freeVar
        _        <- unify ab' (UTerm (a :=> b))
        pure (App f x', wrap b)
    Mono (a :-> b) -> do
        (x', _) <- synCheck ts' x (Mono a)
        pure (App f x', Mono b)
    Mono t -> throwError $ NotAFunction (toSyntax' t) (toSyntax' f) (ppr' x) ts'

    -- If we try to apply to term-apply to a polymorphic function;
    -- we first specialise
    Forall _n ty -> do
        a <- T . UVar <$> freeVar
        sysInferApp ts' (AppTy f a) (instantiate1H a ty) x
  where
    ppr' term' = toSyntax' $ uncurry (\t y -> sthe (toSyntax t) (toSyntax y)) <$> term'

-------------------------------------------------------------------------------
-- Checking
-------------------------------------------------------------------------------

type InfPoly a u = Product (Inf' a) Poly u

unifyPoly
    :: forall b a v. (Eq b, RigidVariable ISym v, ToSyntax a, ToSyntax b, ToSyntax v)
    => Inf (U b v) a
    -> Poly (U b v) -- inferred
    -> Poly (U b v) -- actual
    -> Unify' b v (InfPoly a (U b v))
unifyPoly u (Mono a)     (Mono b)      = do
    ab <- unify (toU a) (toU b)
    return $ Pair (Inf' u) (Mono (T ab))
unifyPoly (Ann (LamTy n u) (Forall m c)) (Forall _ a) (Forall _ b) = withRigid $ do
    -- make a skolem from new variable
    let sko = T (UVar (Left n))
    let a' = instantiate1H sko (fmap (fmap Right) a) -- TODO: fromScopeH
    let b' = instantiate1H sko (fmap (fmap Right) b)
    let c' = instantiate1H sko (fmap (fmap Right) c)
    let u' = instantiate1H sko (fmap (fmap Right) u)
    ip <- unifyPoly (Ann (unChk' u') c') a' b'
    Pair (Inf' u0) ab <- applyBindingsAll ip

    let u1 = flattenInf u0
    let ab1 = flattenPoly ab

    let u2 = toScopeH (Chk' (Inf (first uncomm u1)))
    let ab2 = toScopeH (fmap uncomm ab1)

    let ab3 = Forall m ab2

    return $ Pair (Inf' (Ann (LamTy n u2) ab3)) ab3
unifyPoly _ (Forall _ _) (Forall _ _) = throwError $ SomeErr "not a poly"

-- If we need a monomorphic value, but it's known to be polymorphic:
-- We specialise with fresh metavar.
unifyPoly u (Forall _ b) t@Mono {} = do
    a <- T . UVar <$> freeVar
    unifyPoly (AppTy u a) (instantiate1H a b) t

unifyPoly u a@Mono {} b@Forall {} = throwError $ TypeMismatch
    (toSyntax' a) (toSyntax' b) (toSyntax' u) []

synCheck
    :: forall a b v. (Eq b, RigidVariable ISym v, ToSyntax a, ToSyntax b, ToSyntax v)
    => [SyntaxI]
    -> Chk (U b v) (Poly (U b v), a)
    -> Poly (U b v)
    -> Unify' b v (Chk (U b v) a, Poly (U b v))
synCheck ts term ty = case term of
    Inf u -> do
        (u', t) <- synInfer ts' u
        Pair (Inf' u'') ty' <- unifyPoly u' t ty
        pure (Inf u'', ty')
    Lam n e  -> case ty of
        Mono (T ab) -> do
            a <- UVar <$> freeVar
            b <- UVar <$> freeVar
            _ <- unify ab (UTerm (a :=> b))
            let inst :: Either ISym (Poly (U b v), a) -> Inf (U b v) (Poly (U b v), Either ISym a)
                inst (Left y)         = V (Mono $ T a, Left y)
                inst (Right (ty', x)) = V (ty', Right x)
            let e' = instantiateHEither inst e
            (e'', _) <- synCheck ts' e' (Mono (T b))
            pure (Lam n $ abstractHEither id e'', ty)
        Mono (a :-> b) -> do
            let inst :: Either ISym (Poly (U b v), a) -> Inf (U b v) (Poly (U b v), Either ISym a)
                inst (Left y)         = V (Mono a, Left y)
                inst (Right (ty', x)) = V (ty', Right x)
            let e' = instantiateHEither inst e
            (e'', _) <- synCheck ts' e' (Mono b)
            pure (Lam n $ abstractHEither id e'', ty)
        Mono _    -> throwError $ LambdaNotArrow (toSyntax' ty) pprTerm ts
        Forall {} -> throwError $ LambdaNotArrow (toSyntax' ty) pprTerm ts
    LamTy n e0 -> case ty of
        Forall m s0 -> withRigid $ do
            let e1 = unChk' $ bimap (first (fmap (fmap Right))) comm $ fromScopeH e0
            let s1 = fmap comm $ fromScopeH s0
            (e2, s2) <- synCheck ts' e1 s1
            Pair e3 s3 <- applyBindingsAll (Pair (Chk' e2) s2)
            let e4 = overChk' flattenChk e3
            let s4 = flattenPoly s3
            return
                ( LamTy n $ toScopeH $ fmap uncomm e4
                , Forall m $ toScopeH $ fmap uncomm s4
                )
        _ -> throwError $ PolyNotForall (toSyntax' ty) pprTerm ts

    MkTuple xs -> case ty of
        Mono (T ab) -> do
            xsty' <- for xs $ \x -> do
                a <- UVar <$> freeVar
                (x', _) <- synCheck ts' x (Mono (T a))
                return (x', a)
            let xs' = map fst xsty'
                ab' = map snd xsty'
            ty' <- unify ab (UTerm (TupleF ab'))
            pure (MkTuple xs', Mono (T ty'))

        Mono (Tuple xst) | length xs == length xst -> do
            xsty' <- for (zip xs xst) $ \(x, xt) -> do
                (x', xt') <- synCheck ts' x (Mono xt)
                case xt' of
                    Mono xt'' -> return (x', xt'')
                    Forall {} -> throwError $ SomeErr "poly in mktuple"

            let xs' = map fst xsty'
                ab' = map snd xsty'
            pure (MkTuple xs' , Mono (Tuple ab'))

        Mono _    -> throwError $ PairNotProd (toSyntax' ty) pprTerm ts
        Forall {} -> throwError $ PairNotProd (toSyntax' ty) pprTerm ts

    Split x (Irr xs) b -> do
        (x', xt) <- synInfer ts' x
        case xt of
            Mono (T var) -> do
                ab <- for xs $ \_ -> UVar <$> freeVar
                _ <- unify var (UTerm (TupleF (V.toList ab)))

                let -- inst :: Either (NSym n) (Poly (U b v), a) -> Inf (U b v) (Poly (U b v), Either (NSym n) a)
                    inst (Left n@(NSym y _)) = V (Mono $ T $ ab V.! y , Left n)
                    inst (Right (ty', xx))   = V (ty', Right xx)
                let bb = instantiateHEither inst b
                (bb', tt') <- synCheck ts' bb ty
                pure (Split x' (Irr xs) $ abstractHEither id bb', tt')

            Mono (Tuple xst) -> case equalLength xst xs of
                Nothing -> throwError $ SomeErr "tuple dimensions don't match (synth)"
                Just ab -> do
                    let -- inst :: Either (NSym n) (Poly (U b v), a) -> Inf (U b v) (Poly (U b v), Either (NSym n) a)
                        inst (Left n@(NSym y _)) = V (Mono $ ab V.! y , Left n)
                        inst (Right (ty', xx))   = V (ty', Right xx)

                    let bb = instantiateHEither inst b
                    (bb', tt') <- synCheck ts' bb ty
                    pure (Split x' (Irr xs) $ abstractHEither id bb', tt')

            Mono _    -> throwError $ NotATuple (toSyntax' ty) pprTerm ts'
            Forall {} -> throwError $ NotATuple (toSyntax' ty) pprTerm ts'

  where
    pprTerm = toSyntax' $ uncurry (\t x -> sthe (toSyntax t) (toSyntax x)) <$> term
    ts'     = pprTerm : ts

comm :: Var ISym (U b v) -> U b (Either ISym v)
comm (B n) = UVar (Left n)
comm (F u) = fmap Right u

uncomm :: Either (Either ISym v) b -> Var ISym (U b v)
uncomm (Right b) = F (UTerm (TF b))
uncomm (Left (Left n')) = B n'
uncomm (Left (Right v)) = F (UVar v)

-------------------------------------------------------------------------------
-- Helpers
-------------------------------------------------------------------------------

-- ppr' :: (Functor f, Pretty (f b)) => f (a, b) -> MDoc
-- ppr' x = toSyntax' (snd <$> x)
