module OL1.Expr where

import Prelude ()
import Prelude.Compat

import Bound.ScopeH
import Bound.Var            (Var (..))
import Control.Monad        (ap)
import Control.Monad.Module (Module (..))
import Data.Bifoldable      (Bifoldable (..))
import Data.Bifunctor       (Bifunctor (..))
import Data.Bitraversable   (Bitraversable (..), bifoldMapDefault, bimapDefault)
import Data.Coerce          (coerce)
import Data.Functor.Classes (Eq1 (..), eq1)
import Data.Kind            (Type)
import Data.String          (IsString (..))

import OL1.Name
import OL1.Pretty
import OL1.Smart
import OL1.Type
import OL1.Syntax.FromSyntax

-- | 'Inf'-errable terms
data Inf (b :: Type) (a :: Type)
    -- Variables
    = V a
    -- Functions
    | App (Inf b a) (Chk b a)
    -- Polymorphism
    | AppTy (Inf b a) (Mono b)
    -- Type annotations
    | Ann (Chk b a) (Poly b)
    -- TODO: Record

-- | 'Chk'-able terms.
data Chk (b :: Type) (a :: Type)
    -- Inferrable term
    = Inf (Inf b a)
    -- Function spaces
    | Lam N (ScopeH N (Chk b) (Inf b) a)
    -- Polymorphism
    | LamTy N (ScopeH N (Chk' a) Mono b)
    -- TODO: Record

newtype Inf' a b = Inf' { unInf' :: Inf b a }
newtype Chk' a b = Chk' { unChk' :: Chk b a }

overChk' :: (Chk b a -> Chk d c) -> Chk' a b -> Chk' c d
overChk' = coerce

-------------------------------------------------------------------------------
-- Helpers
-------------------------------------------------------------------------------

peelApp :: Inf b a -> (Inf b a, [Either (Mono b) (Chk b a)])
peelApp (App f x) = case peelApp f of
    ~(f', xs) -> (f', xs ++ [Right x])
peelApp (AppTy x t) = case peelApp x of
    ~(x', xs) -> (x', xs ++ [Left t])
peelApp x = (x, [])

-- | Strips annotations
unAnn :: Inf b a -> Chk b a
unAnn (Ann x _) = x
unAnn x         = Inf x

-------------------------------------------------------------------------------
-- Instances
-------------------------------------------------------------------------------

instance Functor (Inf b)  where fmap = second
instance Functor (Chk b)  where fmap = second
instance Functor (Inf' a) where fmap = second
instance Functor (Chk' a) where fmap = second

instance Applicative (Inf b) where
    pure  = V
    (<*>) = ap

instance Monad (Inf b) where
    return = V
    V x       >>= k = k x
    App f x   >>= k = App (f >>= k) (x >>== k)
    AppTy x t >>= k = AppTy (x >>= k) t
    Ann e t   >>= k = Ann (e >>== k) t

instance Module (Chk b) (Inf b) where
    (>>==) :: forall a c. Chk b a -> (a -> Inf b c) -> Chk b c
    Inf i     >>== k = Inf (i >>= k)
    Lam n b   >>== k = Lam n (b >>== k)
    LamTy n b >>== k = LamTy n $ (overScopeH . overChk') (>>== k') b where
        k' :: a -> Inf (Var N (Mono b)) c
        k' = first (return . return) . k

overScopeH
    :: (f (Var b (m a)) -> f' (Var b' (m' a')))
    -> ScopeH b f m a -> ScopeH b' f' m' a'
overScopeH f (ScopeH s) = ScopeH (f s)

bindInfMono :: Inf b a -> (b -> Mono c) -> Inf c a
bindInfMono (V x) _       = V x
bindInfMono (App f x) k   = App (bindInfMono f k) (bindChkMono x k)
bindInfMono (Ann x t) k   = Ann (bindChkMono x k) (t >>== k)
bindInfMono (AppTy x t) k = AppTy (bindInfMono x k) (t >>= k)

bindChkMono :: Chk b a -> (b -> Mono c) -> Chk c a
bindChkMono (Inf i) k     = Inf (bindInfMono i k)
bindChkMono (LamTy n s) k = LamTy n (s >>== k)
bindChkMono (Lam n s) k   = Lam n $
    overScopeH (fmap (fmap (`bindInfMono` k)) . (`bindChkMono` k)) s

instance Module (Chk' a) Mono where
    Chk' i >>== k = Chk' (bindChkMono i k)

-------------------------------------------------------------------------------
-- Traverse
-------------------------------------------------------------------------------

instance Bifunctor  Inf  where bimap = bimapDefault
instance Bifunctor  Chk  where bimap = bimapDefault
instance Bifunctor  Inf' where bimap = bimapDefault
instance Bifunctor  Chk' where bimap = bimapDefault

instance Bifoldable Inf  where bifoldMap = bifoldMapDefault
instance Bifoldable Chk  where bifoldMap = bifoldMapDefault
instance Bifoldable Inf' where bifoldMap = bifoldMapDefault
instance Bifoldable Chk' where bifoldMap = bifoldMapDefault

instance Foldable (Inf  a) where foldMap = bifoldMap mempty
instance Foldable (Chk  a) where foldMap = bifoldMap mempty
instance Foldable (Inf' a) where foldMap = bifoldMap mempty
instance Foldable (Chk' a) where foldMap = bifoldMap mempty

instance Traversable (Inf a)  where traverse = bitraverse pure
instance Traversable (Chk a)  where traverse = bitraverse pure
instance Traversable (Inf' a) where traverse = bitraverse pure
instance Traversable (Chk' a) where traverse = bitraverse pure

instance Bitraversable Inf' where bitraverse f g = fmap Inf' . bitraverse g f . unInf'
instance Bitraversable Chk' where bitraverse f g = fmap Chk' . bitraverse g f . unChk'

instance Bitraversable Inf where
    bitraverse f g = go where
        go (V x)          = V <$> g x
        go (App h x)      = App <$> go h <*> bitraverse f g x
        go (AppTy h x)    = AppTy <$> go h <*> traverse f x
        go (Ann e b)      = Ann
            <$> bitraverse f g e
            <*> traverse f b

instance Bitraversable Chk where
    bitraverse f g (Inf i)     = Inf <$> bitraverse f g i
    bitraverse f g (Lam n b)   = Lam n
        <$> bitraverseScopeH f f g b
    bitraverse f g (LamTy n b) = LamTy n
        <$> bitransverseScopeH (bitraverse g) traverse f b

-------------------------------------------------------------------------------
-- Eq
-------------------------------------------------------------------------------

instance Eq b => Eq1 (Inf b) where
    liftEq eq = go where
        go (V a)        (V a')         = eq a a'
        go (App f x)    (App f' x')    = go f f' && liftEq eq x x'
        go (AppTy x t)  (AppTy x' t')  = go x x' && t == t'
        go (Ann e t)    (Ann e' t')    = liftEq eq e e' && t == t'

        go V     {}  _ = False
        go App   {}  _ = False
        go AppTy {}  _ = False
        go Ann   {}  _ = False

instance (Eq b) => Eq1 (Chk b) where
    liftEq eq (Inf x)     (Inf y)      = liftEq eq x y
    liftEq eq (Lam n b)   (Lam n' b') = n == n' && liftEq eq b b'
    liftEq eq (LamTy n (ScopeH (Chk' b)))
              (LamTy n' (ScopeH (Chk' b')))  = n == n' &&
        liftEq eq b b'

    liftEq _ Inf   {} _ = False
    liftEq _ Lam   {} _ = False
    liftEq _ LamTy {} _ = False

instance (Eq b, Eq a) => Eq (Inf b a) where (==) = eq1
instance (Eq b, Eq a) => Eq (Chk b a) where (==) = eq1

-------------------------------------------------------------------------------
-- Pretty
-------------------------------------------------------------------------------

instance Pretty b => Pretty1 (Inf b) where
    liftPpr pp x = bitraverse ppr pp x >>= pprInf

instance Pretty b => Pretty1 (Chk b) where
    liftPpr pp x = bitraverse ppr pp x >>= pprChk

instance (Pretty b, Pretty a) => Pretty (Chk b a) where ppr = ppr1
instance (Pretty b, Pretty a) => Pretty (Inf b a) where ppr = ppr1

pprInf :: Inf Doc Doc -> MDoc
pprInf (V x) = return x
pprInf (App f x) = case peelApp f of
    (f', xs) -> sexpr (pprInf f')
        [ either (\u -> pprChar '@' <> pprMono u) pprChk e
        | e <- xs ++ [Right x]
        ]
pprInf (AppTy x t) = case peelApp x of
    (f', xs) -> sexpr (pprInf f')
        [ either (\u -> pprChar '@' <> pprMono u) pprChk e
        | e <- xs ++ [Left t]
        ]
pprInf (Ann e b)   = sexpr (pprText "the") [pprPoly b, pprChk e]

pprChk :: Chk Doc Doc -> MDoc
pprChk (Inf i)     = pprInf i
pprChk (Lam n b)   = pprScopedC n $ \n' ->
    sexpr (pprText "fn") [ return n', pprChk $ instantiate1H (return n') b ]
pprChk (LamTy n b) = pprScopedC n $ \n' ->
    sexpr (pprText "poly") [ return n', pprChk $ unChk' $ instantiate1H (return n') b ]

-------------------------------------------------------------------------------
-- FromSyntax
-------------------------------------------------------------------------------

instance (FromSyntax b, FromSyntax a) => FromSyntax (Inf b a) where
    fromSyntax _ = failure "not implemented"

instance (FromSyntax b, FromSyntax a) => FromSyntax (Chk b a) where
    fromSyntax _ = failure "not implemented"

-------------------------------------------------------------------------------
-- Smart
-------------------------------------------------------------------------------

instance IsString a => IsString (Inf b a) where fromString = V . fromString
instance IsString a => IsString (Chk b a) where fromString = Inf . fromString

instance SLam Chk where
    lam_ x b = Lam (N x) $ abstractHEither k b where
        k n | n == x    = Left (N n)
            | otherwise = Right n

    poly_ t x = LamTy (N t) $ abstractHEither k (Chk' x) where
        k n | n == t    = Left (N n)
            | otherwise = Right n

instance SApp Inf Chk Inf where ($$) = App
instance SApp Inf Chk Chk where f $$ x = Inf (f $$ x)

instance SAppTy Inf Inf where (@@) = AppTy
instance SAppTy Inf Chk where x @@ t =  Inf (x @@ t)
