{-# LANGUAGE OverloadedStrings #-}
module OL1.Synth where

import Bound.ScopeH
import Control.Monad             (void)
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

        expr2 <- specialiseInf expr1
        (expr3, ty) <- synInfer [] expr2
        expr4 <- bitraverse U.applyBindings pure expr3
        ty' <- traverse U.applyBindings ty

        warnings <- for (Map.toList freeVars) $ \(a, v) ->
            NotInScope a . ppr . flattenMono <$> U.applyBindings (U.UVar v)

        return (expr4, ty', warnings)

-------------------------------------------------------------------------------
-- Warning
-------------------------------------------------------------------------------

data Warning a = NotInScope a Doc

instance Pretty a => Pretty (Warning a) where
    ppr (NotInScope a d) = sexpr (PP.text "not-in-scope") [ppr a, d]

-------------------------------------------------------------------------------
-- Specialise
-------------------------------------------------------------------------------

specialiseLeaf :: Eq b => Poly (U b) -> a -> Unify b (Inf (U b) (U b, a))
specialiseLeaf (Mono t)      a = pure $ V (toU t, a)
specialiseLeaf (Forall _ ty) a = do
    t <- T . U.UVar <$> lift U.freeVar
    specialiseLeaf (instantiate1H t ty) a

specialiseInf
    :: Eq b
    => Inf (U b) (Poly (U b), a)
    -> Unify b (Inf (U b) (U b, a))
specialiseInf = fmap join . bitraverse pure (uncurry specialiseLeaf)

-------------------------------------------------------------------------------
-- Generalise
-------------------------------------------------------------------------------

flattenMono :: U b -> Mono (Either U.IntVar b)
flattenMono (U.UVar v)             = T (Left v)
flattenMono (U.UTerm (TF x))       = T (Right x)
flattenMono (U.UTerm (a :=> b))    = flattenMono a :-> flattenMono b
flattenMono (U.UTerm (Skolem n _)) = error $ "escaping skolem" ++ show n -- TODO

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
    :: (Eq b, Pretty a, Pretty b, Monad m)
    => [Doc]
    -> Inf (U b) (U b, a)  -- ^ terms with meta leaves
    -> U.EitherKT Err
        (U.IntBindingT (MonoF b) m)
        (Inf (U b) a, Poly (U b))
synInfer ts term = case term of
    V (ty, a) -> pure (V a, wrap ty)
    Ann x t   -> do
        x' <- synCheck ts' x t
        pure (Ann x' t, t)
    App f x   -> do
        (f', ab) <- synInfer ts' f
        case ab of
            Mono (T ab') -> do
                a        <- U.UVar <$> lift U.freeVar
                b        <- U.UVar <$> lift U.freeVar
                _        <- U.unify ab' (U.UTerm (a :=> b))
                x'       <- synCheck ts' x (wrap a)
                pure (App f' x', wrap b)
            Mono (a :-> b) -> do
                x' <- synCheck ts' x (Mono a)
                pure (App f' x', Mono b)
            _ -> throwError $ NotAFunction (ppr ab) (ppr' f) (ppr' x) ts'
    AppTy x t -> do
        (x', xt) <- synInfer ts' x
        case xt of
            Forall _ b -> pure (AppTy x' t, instantiate1H t b)
            _          -> throwError $ NotAPolyFunction (ppr xt) (ppr' x) (ppr t) ts'
  where
    pprTerm = ppr (fmap (uncurry $ \t x -> sexpr (PP.text "the") [ ppr t , ppr x]) term)
    ts'     = pprTerm : ts

ppr' :: (Functor f, Pretty (f b)) => f (a, b) -> Doc
ppr' x = ppr (snd <$> x)

newSkolem
    :: (Eq b, Pretty b, Monad m)
    => N -> U.EitherKT Err (U.IntBindingT (MonoF b) m) (Mono (U b))
newSkolem n = T . U.UTerm . Skolem n <$> lift U.freeVar

unifyPoly
    :: forall b m. (Monad m, Eq b, Pretty b)
    => Poly (U b)
    -> Poly (U b)
    -> U.EitherKT Err (U.IntBindingT (MonoF b) m) ()
unifyPoly (Mono a)     (Mono b)      = void $
    U.unify (toU a) (toU b)
unifyPoly (Forall n a) (Forall _ b) = void $ do
    -- make a skolem from new variable
    sko <- newSkolem n
    let a' = instantiate1H sko a
    let b' = instantiate1H sko b
    unifyPoly a' b'

unifyPoly a@Mono   {} b = throwError $ TypeMismatch
    (ppr a) (ppr b) (PP.text "?") []
unifyPoly a@Forall {} b = throwError $ TypeMismatch
    (ppr a) (ppr b) (PP.text "?") []

synCheck
    :: forall a b m. (Eq b, Pretty a, Pretty b, Monad m)
    => [Doc]
    -> Chk (U b) (U b, a)
    -> Poly (U b)
    -> U.EitherKT Err (U.IntBindingT (MonoF b) m) (Chk (U b) a)
synCheck ts term ty = case term of
    Inf u -> do
        (u', t) <- synInfer ts' u
        unifyPoly t ty
        pure (Inf u')
    Lam n e  -> case ty of
        Mono (T ab) -> do
            a <- U.UVar <$> lift U.freeVar
            b <- U.UVar <$> lift U.freeVar
            _ <- U.unify ab (U.UTerm (a :=> b))
            let inst :: Either N (U b, a) -> Inf (U b) (U b, Either N a)
                inst (Left y)         = V (a, Left y)
                inst (Right (ty', x)) = V (ty', Right x)
            let e' = instantiateHEither inst e
            e'' <- synCheck ts' e' (Mono (T b))
            pure $ Lam n $ abstractHEither id e''
        Mono (a :-> b) -> do
            let inst :: Either N (U b, a) -> Inf (U b) (U b, Either N a)
                inst (Left y)         = V (toU a, Left y)
                inst (Right (ty', x)) = V (ty', Right x)
            let e' = instantiateHEither inst e
            e'' <- synCheck ts' e' (Mono b)
            pure $ Lam n $ abstractHEither id e''
        Forall {} ->  throwError $ PolyNotForall (ppr ty) pprTerm ts
    LamTy n e -> case ty of
        Forall _m s -> do
            sko <- newSkolem n
            let e' = unChk' $ instantiate1H sko e
            let s' = instantiate1H sko s
            synCheck ts' e' s'
        _ -> throwError $ PolyNotForall (ppr ty) pprTerm ts
  where
    pprTerm = ppr' term
    ts'     = pprTerm : ts
