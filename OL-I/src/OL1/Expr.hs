module OL1.Expr where

import Prelude ()
import Prelude.Compat

import Bound.ScopeH
import Bound.Var            (Var (..))
import Control.Monad        (ap)
import Control.Monad.Module (Module (..))
import Data.Bifoldable      (Bifoldable (..))
import Data.Foldable (foldrM)
import Data.Bifunctor       (Bifunctor (..))
import Data.Bitraversable   (Bitraversable (..), bifoldMapDefault, bimapDefault)
import Data.Coerce          (coerce)
import Data.Functor.Classes (Eq1 (..), eq1)
import Data.Kind            (Type)
import Data.String          (IsString (..))

import OL1.Syntax
import OL1.Syntax.Sym
import OL1.Type

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

-- | 'Chk'-able terms.
data Chk (b :: Type) (a :: Type)
    -- Inferrable term
    = Inf (Inf b a)
    -- Function spaces
    | Lam ISym (ScopeH ISym (Chk b) (Inf b) a)
    -- Polymorphism
    | LamTy ISym (ScopeH ISym (Chk' a) Mono b)

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
        k' :: a -> Inf (Var ISym(Mono b)) c
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
-- FromSyntax
-------------------------------------------------------------------------------

instance (a ~ Sym, b ~ Sym) => FromSyntax (Inf b a) where
    fromSyntax (SSym s)           = return (V s)
    fromSyntax (SList (f : xs))   = fromSyntax f >>= \f' -> go f' xs where
        go g [] = return g
        go g (SAt y : ys) = do
            y' <- fromSyntax y
            go (AppTy g y') ys
        go g (y : ys) = do
            y' <- fromSyntax y
            go (App g y') ys
    fromSyntax (SRList RThe [t, x]) =
        Ann <$> fromSyntax x <*> fromSyntax t

    fromSyntax s = failure $ "not inf: " ++ syntaxToString s

instance (a ~ Sym, b ~ Sym) => FromSyntax (Chk b a) where
    -- fn
    fromSyntax (SRList RFn [SList ss, body]) = do
        body' <- fromSyntax body
        foldrM lam body' ss
      where
        lam :: Syntax -> Chk Sym Sym -> Parser (Chk Sym Sym)
        lam (SSym s)       b = return $ Lam s' (abstractHEither k b) where
            s' = ISym s
            k n | n == s    = Left s'
                | otherwise = Right n

        lam (SAt (SSym s)) b = return $ LamTy s' (abstractHEither k (Chk' b)) where
            s' = ISym s
            k n | n == s    = Left s'
                | otherwise = Right n

        lam s              _ = failure $ "Invalid fn arg" ++ show s -- TODO prety

    fromSyntax (SRList RFn xs) =
        failure $ "invalid fn args: " ++ show xs

    fromSyntax s = Inf <$> fromSyntax s

-------------------------------------------------------------------------------
-- ToSyntax
-------------------------------------------------------------------------------

instance (ToSyntax a, ToSyntax b) => ToSyntax (Inf a b) where
    toSyntax x = bitraverse toSyntax toSyntax x >>= toSyntaxInf

instance (ToSyntax a, ToSyntax b) => ToSyntax (Chk a b) where
    toSyntax x = bitraverse toSyntax toSyntax x >>= toSyntaxChk

toSyntaxInf :: Inf Syntax Syntax -> Printer Syntax
toSyntaxInf (V x)       = return x
toSyntaxInf (App f x)   = sapp (toSyntaxInf f) (toSyntaxChk x)
toSyntaxInf (AppTy x t) = sappTy (toSyntaxInf x) (toSyntaxMono t)
toSyntaxInf (Ann x t)   = sthe (toSyntaxPoly t) (toSyntaxChk x)

toSyntaxChk :: Chk Syntax Syntax -> Printer Syntax
toSyntaxChk (Inf a) = toSyntaxInf a
toSyntaxChk (Lam (ISym n) b) = freshen n $ \s -> sfn
    (toSyntax s)
    (toSyntaxChk (instantiate1H (return (SSym s)) b))
toSyntaxChk (LamTy (ISym n) b) = freshen n $ \s -> spoly
    (toSyntax s)
    (toSyntaxChk (unChk' (instantiate1H (return (SSym s)) b)))

-------------------------------------------------------------------------------
-- Smart
-------------------------------------------------------------------------------

instance IsString a => IsString (Inf b a) where fromString = V . fromString
instance IsString a => IsString (Chk b a) where fromString = Inf . fromString
