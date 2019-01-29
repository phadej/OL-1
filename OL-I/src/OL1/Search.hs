module OL1.Search (search) where

import Bound.ScopeH
import Bound.Var                  (Var (..))
import Control.Monad.State.Strict (StateT (..), evalStateT, get, put)
import Data.Bifunctor             (first)
import Data.Char                  (toLower)
import Data.Fin                   (Fin)
import Data.Foldable              (asum)
import Data.Functor.Foldable      (cata)
import Data.Map                   (Map)
import Data.Nat                   (Nat (..))
import Data.Traversable           (for)
import Data.Vec.Lazy              (Vec (..))

import qualified Data.Fin        as Fin
import qualified Data.Map        as Map
import qualified Data.Text.Short as T
import qualified Data.Vec.Lazy   as V

import OL1.Expr
import OL1.Syntax
import OL1.Syntax.Sym (Sym (..))
import OL1.Type

typeName :: (b -> String) -> Mono b -> Sym
typeName f = Sym . T.pack . cata alg where
    alg (TF x)      = f x
    alg (a :=> b)   = a ++ b
    alg (TupleF xs) = concat xs

search
    :: (Ord b, Show b)
    => (b -> String)
    -> (b -> Maybe (Chk b a))
    -> Poly b
    -> [Chk b a]
search varName known (Mono ty) = searchImpl (typeName varName) known ty
search varName known (Forall n b) = do
    val <- search varName' known' b'
    return $ LamTy n $ toScopeH $ Chk' val
  where
    b' = fromScopeH b

    known' (B _) = Nothing
    known' (F x) = fmap (first F) (known x)

    varName' (B (Irr (Sym s))) = map toLower $ T.unpack s
    varName' (F x) = varName x

searchImpl
    :: forall b a. (Ord b, Show b)
    => (Mono b -> Sym)
    -> (b -> Maybe (Chk b a))
    -> Mono b
    -> [Chk b a]
searchImpl varName known tyGoal =
    concatMap stripL $ evalStateT (emptyCtx |- tyGoal) 0
  where
    known' = fmap (fmap R) . known

    -- We started with empty context,
    -- all names should be abstracted.
    --
    -- We /could/ make this using Var-de-Bruijn too
    -- but it's not worth it.
    -- (I suspect /\-L and =>-L-/\ rules would be tricky)
    --
    stripL = traverse $ \wi -> case wi of
        L _ ->
            -- [] -- we return empty list, to gracefully handle invalid case
            error "panic!" -- panic is useful for debugging though.
        R a -> [a]

    (|-) :: Ctx b a -> Mono b -> StateT Int [] (Chk b (WithInt a))

    -- Atoms in the context:
    --
    -- --------------- Id
    --  Gamma, X |- X
    --
    Ctx ats _ _ [] |- T b
        | Just i <- Map.lookup b ats
        = pure i

    -- Type as is in the context.
    -- This is an optimisation, i.e. this  rule is admissible.
    -- Without it we'll apply other rules, until we reach atoms.
    --
    Ctx _ _ _ ((i, x) : _ctx) |- ty
        | x == ty
        = return i

    -- Note: empty context
    --
    --  Gamma |- A    Gamma |- B
    -- -------------------------- /\-R
    --  Gamma | A /\ B
    --
    -- ------------ T-R
    --  Gamma |- T
    --
    ctx@(Ctx _ _ _ []) |- Tuple tys = do
        xs <- for tys $ \ty -> ctx |- ty
        pure (MkTuple xs)

    -- Note: empty context
    --
    --  Gamma, A |- B
    -- ----------------- =>-R
    --  Gamma |- A => B
    --
    Ctx ats ai ii [] |- (a :-> b) = do
        i <- freshName
        f <- Ctx ats ai ii [(Inf (V (L i)), a)] |- b
        return $ lam_ (varName a) i f

    -- types with known values, essentially Top
    --
    -- ------------ T-R
    --  Gamma |- T
    --
    _ |- T b
        | Just x <- known' b
        = pure x

    -- move atoms int atom part of the context
    Ctx ats ai ii ((i, T b) : ctx) |- ty =
      Ctx (Map.insert b i ats) ai ii ctx |- ty

    --
    --  Gamma |- C
    -- -------------- T-L
    --  Gamma, T |-C
    --
    --  Gamma, A, B |- C
    -- -------------------- /\-L
    --  Gamma, A /\ B |- C
    --
    Ctx ats ai ii ((i, ty'@(Tuple xs')) : ctx) |- ty = V.reifyList xs' $ \xs -> do
        -- we introduce fresh names for variables...
        let names = fmap varName xs
        let inames = Irr names
        fresh <- traverse (const freshName) xs

        -- search in context populated with them
        let ivals = V.zipWith (\ix x -> (Inf $ V $ L ix, x)) fresh xs
        body <- Ctx ats ai ii (V.toList ivals ++ ctx) |- ty

        -- and finally split once.
        let ivars = Map.fromList $ V.toList $ V.izipWith (\f ix s -> (ix, NSym f s)) fresh names
        let abst (L j) | Just k <- Map.lookup j ivars = Left k
            abst x                                    = Right x

        return $ Split (ann i ty') inames $ abstractHEither abst body

    --  Gamma, A => C
    -- ----------------------- =>-L-Atom
    --  Gamma, X, X => A |- C
    --
    -- This only pushes stuff into ai
    Ctx ats ai ii ((i, T x :-> b) : ctx) |- ty =
        Ctx ats (Map.insert (AtomImpl x b) i ai) ii ctx |- ty

    --
    --  Gamma, A |- G
    -- -------------------- =>-L-T
    --  Gamma, T -> A |- G
    --
    --  Gamma, A -> B -> C |- G
    -- ------------------------- =>-L-/\
    --  Gamma, A /\ B -> C |- G
    --
    Ctx ats ai ii ((i, ty'@(Tuple xs' :-> y)) : ctx) |- ty = V.reifyList xs' $ \xs -> do
        -- function type:
        -- from: [a,b,c,d] -> g
        -- to:   a -> (b -> (c -> (d -> g)))
        --
        let fnty = foldr (:->) y xs'
        let names = fmap varName xs
        let i1 = fmap Right i
        let i2 = App (ann i1 ty')
                     (MkTuple $ V.toList $ V.imap (\n _ -> Inf (V (Left n))) $ names)

        Ctx ats ai ii ((nlam_ names $ Inf i2, fnty) : ctx) |- ty

    --
    --  Gamma, B -> C, A |- B    Gamma, C |- G
    -- ---------------------------------------- =>-L-=>
    --  Gamma, ((A -> B) -> C) |- G
    --
    Ctx ats ai ii ((i, (x :-> y) :-> z) : ctx) |- ty =
        Ctx ats ai (Map.insert (ImplImpl x y z) i ii) ctx |- ty

    -- Last rules:
    -- - try to apply deferred =>-L-Atom
    -- - otherwise try =>-L-=> (impl-impl)
    Ctx ats ai ii [] |- ty
        -- L1 completion
        | ((y, yi, ai') : _) <- match
        = Ctx ats ai' ii [(y, yi)] |- ty

        | not (null rest) = asum implImpl
      where
        match = do
            (ai'@(AtomImpl x y), i) <- Map.toList ai
            let xy = T x :-> y
            case Map.lookup x ats of
                Just xi -> return
                    ( Inf (App (ann i xy) xi)  -- term
                    , y                        -- type
                    , Map.delete ai' ai        -- context
                    )
                Nothing -> []

        rest :: [StateT Int [] (Chk b (WithInt a))]
        rest = implImpl

        implImpl = [ implImpl' i xyz | (xyz, i) <- Map.toList ii ]

        implImpl'
            :: Chk b (WithInt a)
            -> ImplImpl b
            -> StateT Int [] (Chk b (WithInt a))
        implImpl' abc xyz@(ImplImpl aT bT cT) = do
            -- modified context
            let ii' = Map.delete xyz ii

            -- some types
            let bcT  = bT :-> cT
            let abT  = aT :-> bT
            let abcT = (aT :-> bT) :-> cT

            -- bc :: b -> c
            -- bc = \b -> abc (\_ -> b)
            let bc = Lam (Irr (varName bT)) $ toScopeH $ Inf $ App (fmap F $ ann abc abcT) $
                     Lam (Irr (varName aT)) $ liftH $ Inf $ V $ B $ Irr $ varName bT

            -- B => C |- A => B
            ab <- Ctx ats ai ii' [(bc, bcT)] |- abT

            -- C |- G
            Ctx ats ai ii' [(Inf $ App (ann abc abcT) ab , cT)] |- ty

    -- otherwise consider an atom again.
    --
    -- - AtomImpl couldn't be simplified: no use
    -- - ImplImpl should be empty
    -- - Atom not in atom part of context
    -- - only option left: no luck.
    --
    Ctx _ _ _ [] |- T _ = StateT $ \_ -> []

freshName :: StateT Int [] Int
freshName = do
    n <- get
    put (succ n)
    return n

-------------------------------------------------------------------------------
-- Amended
-------------------------------------------------------------------------------

data WithInt a
    = L !Int
    | R a
  deriving (Eq, Ord, Show)

-------------------------------------------------------------------------------
-- Context
-------------------------------------------------------------------------------

data Ctx b a = Ctx
    { _ctxAtoms      :: Map b (Chk b (WithInt a))
    , _ctxAtomImpl   :: Map (AtomImpl b) (Chk b (WithInt a))
    , _ctxImplImpl   :: Map (ImplImpl b) (Chk b (WithInt a))
    , _ctxHypothesis :: [(Chk b (WithInt a), Mono b)]
    }

emptyCtx :: Ctx b a
emptyCtx = Ctx Map.empty Map.empty Map.empty []

data AtomImpl b = AtomImpl b (Mono b)
  deriving (Eq, Ord, Show)

data ImplImpl b = ImplImpl !(Mono b) !(Mono b) !(Mono b)
  deriving (Eq, Ord, Show)

-------------------------------------------------------------------------------
-- bound-extras-extras
-------------------------------------------------------------------------------

liftH :: (Functor f, Monad m) => f a -> ScopeH n f m a
liftH s = ScopeH (fmap (F . return) s)

abstract1HEither' :: Sym -> Int -> Chk b (WithInt a) -> ScopeH ISym (Chk b) (Inf b) (WithInt a)
abstract1HEither' n i = abstractHEither $ \x -> case x of
    L j | i == j -> Left (Irr n)
    _            -> Right x

-- | We assume well-typedness.
ann :: Chk b a -> Mono b -> Inf b a
ann (Inf x) _ = x
ann x       t = Ann x (Mono t)

lam_ :: Sym -> Int -> Chk b (WithInt a) -> Chk b (WithInt a)
lam_ n i = Lam (Irr n) . abstract1HEither' n i

nlam_ :: Vec n Sym -> Chk b (Either (Fin n) a) -> Chk b a
nlam_ VNil       b = fmap (either Fin.absurd id) b
nlam_ (x ::: xs) b = Lam (Irr x) (toScopeH b2)
  where
    b1 = fmap (either (k x) (Right . F)) b
    b2 = nlam_ xs b1

    k :: Sym -> Fin ('S m) -> Either (Fin m) (Var ISym a)
    k y Fin.Z     = Right (B (Irr y))
    k _ (Fin.S m) = Left m
