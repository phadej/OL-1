module OL1.Type where

import Bound.ScopeH         (ScopeH, abstractH)
import Control.Monad        (ap)
import Control.Monad.Module (Module (..))
import Data.Functor.Classes (Eq1 (..), eq1)
import Data.String          (IsString (..))
import Data.Text            (Text)

import qualified Text.PrettyPrint.Compact as PP

import OL1.Name
import OL1.Pretty

data Mono a
    = T a
    | Mono a :-> Mono a
    -- TODO: Record
  deriving (Functor, Foldable, Traversable)

instance IsString a => IsString (Mono a) where
    fromString = T . fromString

instance Applicative Mono where
    pure  = T
    (<*>) = ap

instance Monad Mono where
    T a >>= k       = k a
    (a :-> b) >>= k = (a >>= k) :-> (b >>= k)

data Poly a
    = Mono (Mono a)
    | Forall N (ScopeH N Poly Mono a)
  deriving (Functor, Foldable, Traversable)

instance Module Poly Mono where
    Mono x     >>== k = Mono (x >>= k)
    Forall n s >>== k = Forall n (s >>== k)

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

instance Pretty1 Mono where
    liftPpr pp = go where
        go x = case peelArrow x of
            ([], x') -> pp x'
            (xs, x') -> sexpr (PP.text "->") (map go xs ++ [pp x'])

instance Pretty1 Poly where
    liftPpr pp (Mono t)     = liftPpr pp t
    liftPpr pp (Forall n t) = sexpr (PP.text "forall") [ ppr n, liftPpr pp t ]

instance Pretty a => Pretty (Mono a) where ppr = ppr1
instance Pretty a => Pretty (Poly a) where ppr = ppr1

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
