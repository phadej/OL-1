{-# LANGUAGE OverloadedStrings #-}
module OL1.Type where

import Bound.ScopeH              (ScopeH, abstractH, instantiate1H)
import Control.Monad             (ap)
import Control.Monad.Module      (Module (..))
import Control.Unification.Rigid (Unifiable (..))
import Data.Functor.Classes
       (Eq1 (..), Show1 (..), eq1, showsBinaryWith, showsPrec1, showsUnaryWith)
import Data.Functor.Foldable     (Base, Corecursive (..), Recursive (..))
import Data.String               (IsString (..))
import Data.Text                 (Text)

import OL1.Name
import OL1.Pretty
import OL1.Syntax

data Mono a
    = T a
    | Mono a :-> Mono a
    -- TODO: Record
  deriving (Functor, Foldable, Traversable)

infixr 0 :->
infixr 0 :=>

data Poly a
    = Mono (Mono a)
    | Forall N (ScopeH N Poly Mono a)
  deriving (Functor, Foldable, Traversable)

instance IsString a => IsString (Mono a) where
    fromString = T . fromString

instance Applicative Mono where
    pure  = T
    (<*>) = ap

instance Monad Mono where
    T a >>= k       = k a
    (a :-> b) >>= k = (a >>= k) :-> (b >>= k)

instance Module Poly Mono where
    Mono x     >>== k = Mono (x >>= k)
    Forall n s >>== k = Forall n (s >>== k)

-------------------------------------------------------------------------------
-- Eq
-------------------------------------------------------------------------------

instance Eq1 Mono where
    liftEq eq = go where
        go (T a) (T a')          = eq a a'
        go (a :-> b) (a' :-> b') = go a a' && go b b'

        go T     {} _ = False
        go (:->) {} _ = False

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
  deriving (Functor, Foldable, Traversable)

type instance Base (Mono a) = MonoF a

instance Recursive (Mono a) where
    project (T a)     = TF a
    project (a :-> b) = a :=> b

instance Corecursive (Mono a) where
    embed (TF a)    = T a
    embed (a :=> b) = a :-> b

instance Eq a => Unifiable (MonoF a) where
    zipMatch (TF a)       (TF b)
        | a == b    = Just (TF a)
        | otherwise = Nothing
    zipMatch (a :=> b)    (c :=> d) = Just (Right (a, c) :=> Right (b, d))

    zipMatch TF     {} _ = Nothing
    zipMatch (:=>)  {} _ = Nothing

instance Pretty a => Pretty1 (MonoF a) where
    liftPpr _  (TF a)       = ppr a
    liftPpr pp (a :=> b)    = sexpr "->" [pp a, pp b]

-------------------------------------------------------------------------------
-- Pretty
-------------------------------------------------------------------------------

instance Pretty1 Mono where
    liftPpr pp x = traverse pp x >>= pprMono

instance Pretty1 Poly where
    liftPpr pp t = traverse pp t >>= pprPoly

pprMono :: Mono Doc -> MDoc
pprMono x = case peelArrow x of
    ([], x') -> return x'
    (xs, x') -> sexpr "->" (map pprMono xs ++ [return x'])

pprPoly :: Poly Doc -> MDoc
pprPoly (Mono d)     = liftPpr return d
pprPoly (Forall n t) = pprScopedC n $ \n' ->
    sexpr "forall" [ return n', pprPoly $ instantiate1H (return n') t ]

instance Pretty a => Pretty (Mono a) where ppr = ppr1
instance Pretty a => Pretty (Poly a) where ppr = ppr1

-------------------------------------------------------------------------------
-- ToSyntax
-------------------------------------------------------------------------------

instance ToSyntax a => ToSyntax (Mono a) where
    toSyntax (T a) = toSyntax a
    toSyntax (a :-> b) = srlist RFnType [toSyntax a, toSyntax b]

-------------------------------------------------------------------------------
-- FromSyntax
-------------------------------------------------------------------------------

instance FromSyntax a => FromSyntax (Mono a) where
    fromSyntax (SRList RFnType [Juxta a, Juxta b]) =
        (:->) <$> fromSyntax a <*> fromSyntax b
    fromSyntax s = T <$> fromSyntax s

instance FromSyntax a => FromSyntax (Poly a) where
    fromSyntax s = Mono <$> fromSyntax s

-------------------------------------------------------------------------------
-- Utilities
-------------------------------------------------------------------------------

class Forall t where
    forall_ :: Text -> t Text -> Poly Text

instance Forall Mono where
    forall_ v t = Forall (N v) $ abstractH abst (Mono t) where
        abst v' | v == v'   = Just (N v)
                | otherwise = Nothing

peelArrow :: Mono a -> ([Mono a], a)
peelArrow (T a) = ([], a)
peelArrow (a :-> b) = case peelArrow b of
    ~(xs, x) -> (a : xs, x)
