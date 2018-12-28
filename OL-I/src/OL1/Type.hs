{-# LANGUAGE OverloadedStrings #-}
module OL1.Type where

import Bound.ScopeH              (ScopeH, abstractHEither, instantiate1H)
import Control.Monad             (ap)
import Control.Monad.Module      (Module (..))
import Control.Unification.Rigid (Unifiable (..))
import Data.Bifoldable           (Bifoldable (..))
import Data.Bifunctor            (Bifunctor (..))
import Data.Bitraversable
       (Bitraversable (..), bifoldMapDefault, bimapDefault)
import Data.Functor.Classes
       (Eq1 (..), Show1 (..), eq1, showsBinaryWith, showsPrec1, showsUnaryWith)
import Data.Functor.Foldable     (Base, Corecursive (..), Recursive (..))
import Data.String               (IsString (..))

import OL1.Syntax

data Mono a
    = T a
    | Mono a :-> Mono a
    | Tuple [Mono a]
  deriving (Functor, Foldable, Traversable)

infixr 0 :->, :=>

data Poly a
    = Mono (Mono a)
    | Forall ISym (ScopeH ISym Poly Mono a)
  deriving (Functor, Foldable, Traversable)

instance IsString a => IsString (Mono a) where
    fromString = T . fromString

instance Applicative Mono where
    pure  = T
    (<*>) = ap

instance Monad Mono where
    T a >>= k       = k a
    (a :-> b) >>= k = (a >>= k) :-> (b >>= k)
    Tuple as  >>= k = Tuple (map (>>= k) as)

instance Module Poly Mono where
    Mono x     >>== k = Mono (x >>= k)
    Forall n s >>== k = Forall n (s >>== k)

-------------------------------------------------------------------------------
-- Eq
-------------------------------------------------------------------------------

instance Eq1 Mono where
    liftEq eq = go where
        go (T a)     (T a')      = eq a a'
        go (a :-> b) (a' :-> b') = go a a' && go b b'
        go (Tuple x) (Tuple x')  = liftEq go x x'

        go T     {} _ = False
        go (:->) {} _ = False
        go Tuple {} _ = False

instance Eq1 Poly where
    liftEq eq (Mono a)     (Mono a')     = liftEq eq a a'
    liftEq eq (Forall _ s) (Forall _ s') = liftEq eq s s'

    liftEq _ Mono   {} _ = False
    liftEq _ Forall {} _ = False

instance Eq a => Eq (Mono a) where (==) = eq1
instance Eq a => Eq (Poly a) where (==) = eq1

-------------------------------------------------------------------------------
-- Show
-------------------------------------------------------------------------------

instance Show1 Mono where
    liftShowsPrec sp _ d (T x) = showsUnaryWith
        sp
        "T" d x
    liftShowsPrec sp sl d (a :-> b) = showParen (d > 0)
        $ liftShowsPrec sp sl 1 a
        . showString " :-> "
        . liftShowsPrec sp sl 0 b
    liftShowsPrec sp sl d (Tuple x) = showsUnaryWith
        (liftShowsPrec (liftShowsPrec sp sl) (liftShowList sp sl))
        "Tuple" d x

instance Show1 Poly where
    liftShowsPrec sp sl d (Mono x) = showsUnaryWith
        (liftShowsPrec sp sl)
        "Mono" d x
    liftShowsPrec sp sl d (Forall x y) = showsBinaryWith
        showsPrec
        (liftShowsPrec sp sl)
        "Forall" d x y

instance Show a => Show (Mono a) where showsPrec = showsPrec1
instance Show a => Show (Poly a) where showsPrec = showsPrec1

-------------------------------------------------------------------------------
-- MonoF
-------------------------------------------------------------------------------

data MonoF a b
    = TF a
    | b :=> b
    | TupleF [b]
  deriving (Functor, Foldable, Traversable)

type instance Base (Mono a) = MonoF a

instance Recursive (Mono a) where
    project (T a)     = TF a
    project (a :-> b) = a :=> b
    project (Tuple x) = TupleF x

instance Corecursive (Mono a) where
    embed (TF a)     = T a
    embed (a :=> b)  = a :-> b
    embed (TupleF x) = Tuple x

instance Bifunctor MonoF where bimap = bimapDefault
instance Bifoldable MonoF where bifoldMap = bifoldMapDefault

instance Bitraversable MonoF where
    bitraverse f _ (TF a)     = TF <$> f a
    bitraverse _ g (a :=> b)  = (:=>) <$> g a <*> g b
    bitraverse _ g (TupleF x) = TupleF <$> traverse g x

instance Eq a => Unifiable (MonoF a) where
    zipMatch (TF a)       (TF b)
        | a == b    = Just (TF a)
        | otherwise = Nothing
    zipMatch (a :=> b)  (c :=> d)  = Just (Right (a, c) :=> Right (b, d))
    zipMatch (TupleF x) (TupleF y) = TupleF <$> zipMatch x y

    zipMatch TF     {} _ = Nothing
    zipMatch (:=>)  {} _ = Nothing
    zipMatch TupleF {} _ = Nothing

-------------------------------------------------------------------------------
-- ToSyntax
-------------------------------------------------------------------------------

instance ToSyntax a => ToSyntax (Mono a) where
    toSyntax a = traverse toSyntax a >>= toSyntaxMono

instance ToSyntax a => ToSyntax1 (MonoF a) where
    liftToSyntax s a = bitraverse toSyntax (return . s) a >>= toSyntaxMonoF

instance ToSyntax a => ToSyntax (Poly a) where
    toSyntax a = traverse toSyntax a >>= toSyntaxPoly

toSyntaxMono :: Mono Syntax -> Printer Syntax
toSyntaxMono = cata toSyntaxMonoF

toSyntaxMonoF :: MonoF Syntax (Printer Syntax) -> Printer Syntax
toSyntaxMonoF (TF a)     = return a
toSyntaxMonoF (a :=> b)  = sarrow a b
toSyntaxMonoF (TupleF b) = stuple b

toSyntaxPoly :: Poly Syntax -> Printer Syntax
toSyntaxPoly (Mono a)     = toSyntaxMono a
toSyntaxPoly (Forall s a) = freshenI s $ \s' ->
    let s'' = SSym s'
    in sforall (return s'') $ toSyntax $ instantiate1H (return s'') a

-------------------------------------------------------------------------------
-- FromSyntax
-------------------------------------------------------------------------------

instance a ~ Sym => FromSyntax (Mono a) where
    fromSyntax (SRList RFnType [])     = return (Tuple [])
    fromSyntax (SRList RFnType [a])    = fromSyntax a
    fromSyntax (SRList RFnType (a:bs)) = do
        bs' <- fromSyntax (SRList RFnType bs)
        (:->) <$> fromSyntax a <*> pure bs'
    fromSyntax (SRList RTuple xs)     = Tuple <$> traverse fromSyntax xs

    fromSyntax s = T <$> fromSyntax s

instance a ~ Sym => FromSyntax (Poly a) where
    fromSyntax (SRList RFnType (SAt (SSym x) : xs)) = fromSyntaxPoly x xs
    fromSyntax s                                    = Mono <$> fromSyntax s

fromSyntaxPoly :: Sym -> [Syntax] -> Parser (Poly Sym)
fromSyntaxPoly s xs = do
    ys <- fromSyntax (SRList RFnType xs)
    return $ Forall s' $ abstractHEither k ys
  where
    s' = Irr s

    k n | n == s    = Left s'
        | otherwise = Right n
