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
import Data.Foldable        (foldrM)
import Data.Kind            (Type)
import Data.String          (IsString (..))
import Data.Vec.Lazy        (Vec (..), reifyList, universe, (!))

import qualified Data.Map.Strict as Map
import qualified Data.Vec.Lazy   as V

import OL1.Syntax
import OL1.Type

-- | 'Inf'-errable terms
data Inf (b :: Type) (a :: Type)
    -- | Variables
    = V a
    -- | Functions
    | App (Inf b a) (Chk b a)
    -- |Polymorphism
    | AppTy (Inf b a) (Mono b)
    -- | Type annotations
    | Ann (Chk b a) (Poly b)

-- | 'Chk'-able terms.
data Chk (b :: Type) (a :: Type) where
    -- Inferrable term
    Inf :: Inf b a -> Chk b a
    -- Function spaces
    Lam :: ISym -> ScopeH ISym (Chk b) (Inf b) a -> Chk b a
    -- Polymorphism
    LamTy :: ISym -> ScopeH ISym (Chk' a) Mono b -> Chk b a

    -- Tuple constructor
    MkTuple :: [Chk b a] -> Chk b a

    -- Tuple split
    Split :: Inf b a -> Irr (Vec n Sym) -> ScopeH (NSym n) (Chk b) (Inf b) a -> Chk b a

newtype Inf' a b = Inf' { unInf' :: Inf b a }
newtype Chk' a b = Chk' { unChk' :: Chk b a }

overChk' :: (Chk b a -> Chk d c) -> Chk' a b -> Chk' c d
overChk' = coerce

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

    V x         >>= k = k x
    App f x     >>= k = App (f >>= k) (x >>== k)
    AppTy x t   >>= k = AppTy (x >>= k) t
    Ann e t     >>= k = Ann (e >>== k) t

instance Module (Inf b) (Inf b) where
    (>>==) = (>>=)

instance Module (Chk b) (Inf b) where
    (>>==) :: forall a c. Chk b a -> (a -> Inf b c) -> Chk b c
    Inf i       >>== k = Inf (i >>= k)
    Lam n b     >>== k = Lam n (b >>== k)
    LamTy n b   >>== k = LamTy n $ (overScopeH . overChk') (>>== k') b where
        k' :: a -> Inf (Var ISym(Mono b)) c
        k' = first (return . return) . k

    Split x xs b >>== k = Split (x >>= k) xs (b >>== k)
    MkTuple xs  >>== k = MkTuple (map (>>== k) xs)

overScopeH
    :: (f (Var b (m a)) -> f' (Var b' (m' a')))
    -> ScopeH b f m a -> ScopeH b' f' m' a'
overScopeH f (ScopeH s) = ScopeH (f s)

bindInfMono :: Inf b a -> (b -> Mono c) -> Inf c a
bindInfMono (V x)       _ = V x
bindInfMono (App f x)   k = App (bindInfMono f k) (bindChkMono x k)
bindInfMono (Ann x t)   k = Ann (bindChkMono x k) (t >>== k)
bindInfMono (AppTy x t) k = AppTy (bindInfMono x k) (t >>= k)

bindChkMono :: Chk b a -> (b -> Mono c) -> Chk c a
bindChkMono (Inf i)      k = Inf (bindInfMono i k)
bindChkMono (LamTy n s)  k = LamTy n (s >>== k)
bindChkMono (Lam n s)    k = Lam n $ overScopeH
    (fmap (fmap (`bindInfMono` k)) . (`bindChkMono` k))
    s
bindChkMono (Split x xs b) k = Split (bindInfMono x k) xs $ overScopeH
    (fmap (fmap (`bindInfMono` k)) . (`bindChkMono` k))
    b
bindChkMono (MkTuple xs) k = MkTuple (map (flip bindChkMono k) xs)

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
    bitraverse _ g (V x)       = V <$> g x
    bitraverse f g (App h x)   = App <$> bitraverse f g h <*> bitraverse f g x
    bitraverse f g (AppTy h x) = AppTy <$> bitraverse f g h <*> traverse f x
    bitraverse f g (Ann e b)   = Ann <$> bitraverse f g e <*> traverse f b


instance Bitraversable Chk where
    bitraverse f g (Inf i)       = Inf <$> bitraverse f g i
    bitraverse f g (Lam n b)     = Lam n
        <$> bitraverseScopeH f f g b
    bitraverse f g (LamTy n b)   = LamTy n
        <$> bitransverseScopeH (bitraverse g) traverse f b
    bitraverse f g (Split x xs b) = Split
        <$> bitraverse f g x
        <*> pure xs
        <*> bitraverseScopeH f f g b
    bitraverse f g (MkTuple xs)  = MkTuple <$> traverse (bitraverse f g) xs

-------------------------------------------------------------------------------
-- FromSyntax
-------------------------------------------------------------------------------

instance (a ~ Sym, b ~ Maybe Sym) => FromSyntax (Inf b a) where
    fromSyntax = fromSyntaxInf

instance (a ~ Sym, b ~ Maybe Sym) => FromSyntax (Chk b a) where
    fromSyntax = fromSyntaxChk

fromSyntaxInf :: Spanned SyntaxS -> Parser (Inf (Maybe Sym) Sym)

-- symbols
fromSyntaxInf (SSym s :~ _)         = return (V s)

-- lists
fromSyntaxInf (SList [] :~ _)       = return $ Ann (MkTuple []) (Mono (Tuple []))
fromSyntaxInf (SList (f : xs) :~ _) = fromSyntaxInf f >>= \f' -> go f' xs where
    go g [] = return g
    go g (SAt y :~ _ : ys) = do
        y' <- fromSyntaxMono y
        go (AppTy g (fmap Just y')) ys
    go g (y : ys) = do
        y' <- fromSyntaxChk y
        go (App g y') ys
fromSyntaxInf (SRList (RThe :~ _) [t, x] :~ _) = do
    x' <- fromSyntaxChk x
    t' <- fromSyntaxPoly t
    return (Ann x' (fmap Just t'))
fromSyntaxInf (SRList (RThe :~ ann) _ :~ _) = failFixit ann
    "'the' takes exactly two arguments"

-- at
fromSyntaxInf (SAt _ :~ ann) = failFixit ann "Unexpected @at"

-- rest Reserved: fail
fromSyntaxInf (SRList (r :~ ann) _ :~ _) = failFixit ann $
    "Unexpected " ++ reservedToString r ++ " in term"


fromSyntaxInf' :: Spanned SyntaxS -> Parser (Inf (Maybe Sym) Sym)
fromSyntaxInf' s = do
    x <- fromSyntaxChk s
    return $ case x of
        Inf x' -> x'
        _      -> Ann x (Mono (T Nothing))

fromSyntaxChk :: Spanned SyntaxS -> Parser (Chk (Maybe Sym) Sym)
-- fn
fromSyntaxChk (SRList (RFn :~ _) [SList ss :~ _, body] :~ _) = do
    body' <- fromSyntaxChk body
    foldrM lam body' ss
  where
    lam :: Spanned SyntaxS -> Chk (Maybe Sym) Sym -> Parser (Chk (Maybe Sym) Sym)
    lam (SSym s :~ _)       b = return $ Lam s' (abstractHEither k b) where
        s' = Irr s
        k n | n == s    = Left s'
            | otherwise = Right n

    lam (SAt (SSym s :~ _) :~ _) b = return $ LamTy s' (abstractHEither k (Chk' b)) where
        s' = Irr s
        k n | n == Just s = Left s'
            | otherwise   = Right n

    lam (_ :~ ann)         _ = failFixit ann
        "fn arguments should be symbols or @symbols"

fromSyntaxChk (SRList (RFn :~ ann) _ :~ _) = failFixit ann
    "Invalid fn arguments"

-- Tuples
fromSyntaxChk (SRList (RTuple :~ _) xs :~ _) = MkTuple <$> traverse fromSyntaxChk xs

fromSyntaxChk (SRList (RSplit :~ _) [x, SList xs :~ _, body] :~ _) = do
    xs' <- traverse fromSyntaxSym xs
    x' <- fromSyntaxInf' x
    body' <- fromSyntaxChk body

    return $ reifyList xs' $ \xs'' ->
        let xsm = Map.fromList $ V.toList (V.zipWith (,) xs'' universe)
            k n = case Map.lookup n xsm of
                Just i  -> Left (NSym i n)
                Nothing -> Right n
        in Split x' (Irr xs'') $ abstractHEither k body'
  where
    fromSyntaxSym :: Spanned SyntaxS -> Parser Sym
    fromSyntaxSym (SSym s :~ _)   = return s
    fromSyntaxSym (_      :~ ann) = failFixit ann
        "split variables should be symbols"

fromSyntaxChk (SRList (RSplit :~ ann) _ :~ _)  =
    failFixit ann "Invalid split arguments"

-- Inf
fromSyntaxChk s = Inf <$> fromSyntaxInf s

-------------------------------------------------------------------------------
-- ToSyntax
-------------------------------------------------------------------------------

instance (ToSyntax a, ToSyntax b) => ToSyntax (Inf a b) where
    toSyntax x = bitraverse toSyntax toSyntax x >>= toSyntaxInf

instance (ToSyntax a, ToSyntax b) => ToSyntax (Chk a b) where
    toSyntax x = bitraverse toSyntax toSyntax x >>= toSyntaxChk

toSyntaxInf :: Inf SyntaxI SyntaxI -> Printer SyntaxI
toSyntaxInf (V x)             = return x
toSyntaxInf (App f x)         = sapp (toSyntaxInf f) (toSyntaxChk x)
toSyntaxInf (AppTy x t)       = sappTy (toSyntaxInf x) (toSyntaxMono t)
toSyntaxInf (Ann x t)         = sthe (toSyntaxPoly t) (toSyntaxChk x)

toSyntaxChk :: Chk SyntaxI SyntaxI -> Printer SyntaxI
toSyntaxChk (Inf a) = toSyntaxInf a
toSyntaxChk (Lam (Irr n) b) = freshen n $ \s -> sfn
    (toSyntax s)
    (toSyntaxChk (instantiate1H (return (SSym s)) b))
toSyntaxChk (LamTy (Irr n) b) = freshen n $ \s -> spoly
    (toSyntax s)
    (toSyntaxChk (unChk' (instantiate1H (return (SSym s)) b)))
toSyntaxChk (MkTuple xs) = stuple (map toSyntaxChk xs)
toSyntaxChk (Split x (Irr xs) b) = freshenMany xs $ \ss -> scase
    (toSyntaxInf x)
    (map toSyntax $ V.toList ss)
    (toSyntaxChk (instantiateH (\(NSym i _) -> return $ SSym $ xs ! i) b))

-------------------------------------------------------------------------------
-- Smart
-------------------------------------------------------------------------------

instance IsString a => IsString (Inf b a) where fromString = V . fromString
instance IsString a => IsString (Chk b a) where fromString = Inf . fromString

unAnn :: Inf b a -> Chk b a
unAnn (Ann x _) = x
unAnn x         = Inf x
