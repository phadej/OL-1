{-# LANGUAGE OverloadedStrings #-}
module OL1.Synth where

import Bound.ScopeH
import Control.Monad.Error.Class (MonadError (..))
import Control.Monad.Module      (Module (..))
import Control.Monad.State
import Control.Monad.Trans.Class (lift)
import Data.Bifoldable           (bifoldMap)
import Data.Bifunctor            (Bifunctor (..))
import Data.Bitraversable        (bitraverse)
import Data.Functor.Identity     (Identity (..))
import Data.Traversable          (for)

import OL1.Error
import OL1.Expr
import OL1.Name
import OL1.Pretty
import OL1.Type

import qualified Control.Monad.EitherK      as U
import qualified Control.Unification        as U
import qualified Control.Unification.IntVar as U
import qualified Data.IntSet                as IS
import qualified Data.Map.Strict            as Map
import qualified Text.PrettyPrint.Compact   as PP

-------------------------------------------------------------------------------
-- Unifiable mono types
-------------------------------------------------------------------------------

data MonoF a b
    = TF a
    | Skolem N U.IntVar
    | b :=> b
  deriving (Functor, Foldable, Traversable)

instance Eq a => U.Unifiable (MonoF a) where
    zipMatch (TF a)       (TF b)
        | a == b    = Just (TF a)
        | otherwise = Nothing
    zipMatch (Skolem n i) (Skolem _ j)
        | i == j    = Just (Skolem n i)
        | otherwise = Nothing
    zipMatch (a :=> b)    (c :=> d) = Just (Right (a, c) :=> Right (b, d))

    zipMatch TF     {} _ = Nothing
    zipMatch Skolem {} _ = Nothing
    zipMatch (:=>)  {} _ = Nothing

instance Pretty a => Pretty1 (MonoF a) where
    liftPpr _  (TF a)       = ppr a
    liftPpr pp (a :=> b)    = sexpr (PP.text "->") [pp a, pp b]
    liftPpr _  (Skolem n i) = sexpr (PP.text "skolem") [ ppr n, ppr i ]

type U b = U.UTerm (MonoF b) U.IntVar

toU :: Mono (U b) -> U b
toU (T a)     = a
toU (a :-> b) = U.UTerm (toU a :=> toU b)

-------------------------------------------------------------------------------
-- High-level interface
-------------------------------------------------------------------------------

type Unify b = U.EitherKT Err (U.IntBindingT (MonoF b) Identity)

synth
    :: forall a b. (Ord a, Eq b, Pretty a, Pretty b)
    => (a -> Maybe (Poly b))
    -> Inf (Maybe b) a
    -> Either Err (Inf b a, [Warning a])
synth ctx
    = fmap (\(x, t, ws) -> (generalise x t, ws))
    . runIdentity
    . U.evalIntBindingT
    . U.runEitherKT
    . action
  where
    action
        :: Inf (Maybe b) a
        -> Unify b (Inf (U b) a, Poly (U b), [Warning a])
    action expr0 = do
        (expr1, freeVars) <- flip runStateT Map.empty $ do
            let freeA a = case ctx a of
                    Just ty -> pure (fmap (U.UTerm . TF) ty, a)
                    Nothing -> do
                        freeVars <- get
                        case Map.lookup a freeVars of
                            Just v -> pure (Mono (T (U.UVar v)), a)
                            Nothing -> do
                                v <- lift (lift U.freeVar)
                                put (Map.insert a v freeVars)
                                pure (Mono (T (U.UVar v)), a)
            let freeB (Just b) = pure (U.UTerm (TF b))
                freeB Nothing  = U.UVar <$> lift (lift U.freeVar)
            bitraverse freeB freeA expr0

        -- there is no expr2
        (expr3, ty) <- synInfer [] expr1
        expr4 <- bitraverse U.applyBindings pure expr3
        ty' <- traverse U.applyBindings ty

        warnings <- for (Map.toList freeVars) $ \(a, v) ->
            NotInScope a . ppr . flattenMonoDoc <$> U.applyBindings (U.UVar v)

        return (expr4, ty', warnings)

-------------------------------------------------------------------------------
-- Warning
-------------------------------------------------------------------------------

data Warning a = NotInScope a Doc

instance Pretty a => Pretty (Warning a) where
    ppr (NotInScope a d) = sexpr (PP.text "not-in-scope") [ppr a, d]

-------------------------------------------------------------------------------
-- Generalise
-------------------------------------------------------------------------------

flattenMono :: U b -> Mono (Either U.IntVar b)
flattenMono (U.UVar v)             = T (Left v)
flattenMono (U.UTerm (TF x))       = T (Right x)
flattenMono (U.UTerm (a :=> b))    = flattenMono a :-> flattenMono b
flattenMono (U.UTerm (Skolem n _)) = error $ "panic! escaping skolem" ++ show n -- TODO

flattenMonoDoc :: Pretty b => U b -> Mono (Either U.IntVar Doc)
flattenMonoDoc (U.UVar v)             = T (Left v)
flattenMonoDoc (U.UTerm (TF x))       = T (Right (ppr x))
flattenMonoDoc (U.UTerm (a :=> b))    = flattenMonoDoc a :-> flattenMonoDoc b
flattenMonoDoc (U.UTerm (Skolem n v)) = T (Right (sexpr (PP.text "skolem") [ppr n, ppr v]))

flattenPoly :: Poly (U b) -> Poly (Either U.IntVar b)
flattenPoly t = t >>== flattenMono

flattenInf :: Inf (U b) a -> Inf (Either U.IntVar b) a
flattenInf = flip bindInfMono flattenMono

flattenChk :: Chk (U b) a -> Chk (Either U.IntVar b) a
flattenChk = flip bindChkMono flattenMono

generalise :: Inf (U b) a -> Poly (U b) -> Inf b a
generalise x0 t0 = first fromRight' $ fst $ foldr (uncurry . f) (x1, t1) (IS.toList intVars) -- error $ show intVars
  where
    x1 = flattenInf x0
    t1 = flattenPoly t0

    fromRight' :: Either U.IntVar b -> b
    fromRight' (Right b) = b
    fromRight' (Left i)  = error $ "panic! Ungeneralised variable " ++ show i

    intVars :: IS.IntSet
    intVars = mappend
        (bifoldMap sing (const mempty) x1)
        (foldMap sing t1)

    sing (Left (U.IntVar n)) = IS.singleton n
    sing (Right _)           = IS.empty

    f :: Int ->  Inf (Either U.IntVar b) a -> Poly (Either U.IntVar b)
             -> (Inf (Either U.IntVar b) a,   Poly (Either U.IntVar b))
    f v x t = (Ann x' t', t')  where
        n = N "?"

        x' = LamTy n $ abstractH abst $ Chk' $ unAnn x

        t' = Forall n $ abstractH abst t

        abst (Left (U.IntVar v'))
            | v == v'   = Just n
            | otherwise = Nothing
        abst (Right _)  = Nothing

-------------------------------------------------------------------------------
-- Inference
-------------------------------------------------------------------------------

-- TODO: make constraint type, collect them

wrap :: U b -> Poly (U b)
wrap = Mono . T

synInfer
    :: (Eq b, Pretty a, Pretty b)
    => [Doc]
    -> Inf (U b) (Poly (U b), a)  -- ^ terms with meta leaves
    -> Unify b (Inf (U b) a, Poly (U b))
synInfer ts term = case term of
    V (ty, a) -> pure (V a, ty)
    Ann x t   -> do
        x' <- synCheck ts' x t
        pure (Ann x' t, t)
    App f x   -> do
        (f', ab) <- synInfer ts' f
        sysInferApp ts' f' ab x
    AppTy x t -> do
        (x', xt) <- synInfer ts' x
        case xt of
            Forall _ b -> pure (AppTy x' t, instantiate1H t b)
            _          -> throwError $ NotAPolyFunction (ppr xt) (ppr' x) (ppr t) ts'
  where
    pprTerm = ppr (fmap (uncurry $ \t x -> sexpr (PP.text "the") [ ppr t , ppr x]) term)
    ts'     = pprTerm : ts

sysInferApp
    :: (Eq b, Pretty a, Pretty b)
    => [Doc]
    -> Inf (U b) a
    -> Poly (U.UTerm (MonoF b) U.IntVar)
    -> Chk (U b) (Poly (U b), a)
    -> Unify b (Inf (U b) a, Poly (U b))
sysInferApp ts' f ab x = case ab of
    Mono (T ab') -> do
        a        <- U.UVar <$> lift U.freeVar
        b        <- U.UVar <$> lift U.freeVar
        _        <- U.unify ab' (U.UTerm (a :=> b))
        x'       <- synCheck ts' x (wrap a)
        pure (App f x', wrap b)
    Mono (a :-> b) -> do
        x' <- synCheck ts' x (Mono a)
        pure (App f x', Mono b)
    -- If we try to apply to term-apply to a polymorphic function;
    -- we first specialise
    Forall _n ty -> do
        a <- T . U.UVar <$> lift U.freeVar
        sysInferApp ts' (AppTy f a) (instantiate1H a ty) x

ppr' :: (Functor f, Pretty (f b)) => f (a, b) -> Doc
ppr' x = ppr (snd <$> x)

newSkolem
    :: (Eq b, Pretty b)
    => N -> Unify b (U b)
newSkolem n = U.UTerm . Skolem n <$> lift U.freeVar

eqSkolem :: U b -> U b -> Bool
eqSkolem (U.UTerm (Skolem _ a)) (U.UTerm (Skolem _ b)) = a == b
eqSkolem _ _ = False

unifyPoly
    :: forall b a. (Eq b, Pretty b)
    => Inf (U b) a
    -> Poly (U b) -- inferred
    -> Poly (U b) -- actual
    -> Unify b (Inf (U b) a)
unifyPoly u (Mono a)     (Mono b)      = do
    _ <- U.unify (toU a) (toU b)
    return u
unifyPoly u (Forall n a) (Forall _ b) = do
    -- make a skolem from new variable
    sko <- T <$> newSkolem n
    let a' = instantiate1H sko a
    let b' = instantiate1H sko b
    unifyPoly u a' b'

-- If we need a monomorphic value, but it's known to be polymorphic:
-- We specialise with fresh metavar.
unifyPoly u (Forall _ b) t@Mono {} = do
    a <- T . U.UVar <$> lift U.freeVar
    unifyPoly (AppTy u a) (instantiate1H a b) t

unifyPoly _ a@Mono {} b@Forall {} = throwError $ TypeMismatch
    (ppr a) (ppr b) (PP.text "?") []

synCheck
    :: forall a b. (Eq b, Pretty a, Pretty b)
    => [Doc]
    -> Chk (U b) (Poly (U b), a)
    -> Poly (U b)
    -> Unify b (Chk (U b) a)
synCheck ts term ty = case term of
    Inf u -> do
        (u', t) <- synInfer ts' u
        u'' <- unifyPoly u' t ty
        pure (Inf u'')
    Lam n e  -> case ty of
        Mono (T ab) -> do
            a <- U.UVar <$> lift U.freeVar
            b <- U.UVar <$> lift U.freeVar
            _ <- U.unify ab (U.UTerm (a :=> b))
            let inst :: Either N (Poly (U b), a) -> Inf (U b) (Poly (U b), Either N a)
                inst (Left y)         = V (Mono $ T a, Left y)
                inst (Right (ty', x)) = V (ty', Right x)
            let e' = instantiateHEither inst e
            e'' <- synCheck ts' e' (Mono (T b))
            pure $ Lam n $ abstractHEither id e''
        Mono (a :-> b) -> do
            let inst :: Either N (Poly (U b), a) -> Inf (U b) (Poly (U b), Either N a)
                inst (Left y)         = V (Mono a, Left y)
                inst (Right (ty', x)) = V (ty', Right x)
            let e' = instantiateHEither inst e
            e'' <- synCheck ts' e' (Mono b)
            pure $ Lam n $ abstractHEither id e''
        Forall {} ->  throwError $ PolyNotForall (ppr ty) pprTerm ts
    LamTy n e0 -> case ty of
        Forall m s -> do
            sko <- newSkolem n
            let e1 = unChk' $ instantiate1H (T sko) e0
            let s' = instantiate1H (T sko) s
            e2 <- synCheck ts' e1 s'
            let abst :: U b -> Maybe N
                abst x | eqSkolem x sko = Just m
                       | otherwise = Nothing
            return $ LamTy n $ abstractH abst $ Chk' e2
        _ -> throwError $ PolyNotForall (ppr ty) pprTerm ts
  where
    pprTerm = ppr' term
    ts'     = pprTerm : ts
