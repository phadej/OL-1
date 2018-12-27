module OL1.Syntax.ToSyntax where

-- import Bound.Scope.Simple         (Scope (..))
-- import Bound.ScopeH               (ScopeH (..))
-- import Bound.ScopeT               (ScopeT (..))

import Bound.Var                  (Var (..))
import Control.Monad.State.Strict
import Control.Unification.Rigid  (MetaVar (..), UTerm (..))
import Data.Char                  (isDigit)
import Data.String                (IsString (..))
import Data.Text.Short            (ShortText)
import Data.Void                  (Void, absurd)

import qualified Data.Set        as Set
import qualified Data.Text.Short as T

import OL1.Syntax.Sym
import OL1.Syntax.Type

-------------------------------------------------------------------------------
-- Types
-------------------------------------------------------------------------------

type SyntaxM = Printer Syntax

-- | State of pretty-printer's "used" symbols
type S = Set.Set U

newtype Printer a = Printer { unPrinter :: State S a }
  deriving newtype (Functor, Applicative, Monad)

runPrinter :: Printer a -> a
runPrinter (Printer m) = evalState m Set.empty

-------------------------------------------------------------------------------
-- Classes
-------------------------------------------------------------------------------

class ToSyntax a where
    toSyntax :: a -> SyntaxM

class ToSyntax1 f where
    liftToSyntax :: (a -> SyntaxM) -> f a -> SyntaxM

instance ToSyntax Sym where
    toSyntax = return . SSym

instance ToSyntax ISym where
    toSyntax (ISym s) = return (SSym (Sym s))

instance ToSyntax Syntax where
    toSyntax = return

instance ToSyntax a => ToSyntax (Printer a) where
    toSyntax = (>>= toSyntax)

toSyntax1 :: (ToSyntax1 f, ToSyntax a) => f a -> SyntaxM
toSyntax1 = liftToSyntax toSyntax

-------------------------------------------------------------------------------
-- Freshen
-------------------------------------------------------------------------------

-- | Make fresh symbol variant.
freshen :: Sym -> (Sym -> Printer a) -> Printer a
freshen (Sym s) f = Printer $ do
    xs <- get
    let u = freshU xs (genU (toU s))
    put (Set.insert u xs)
    x <- unPrinter (f (fromString (fromU u)))
    modify' (Set.delete u)
    return x

-------------------------------------------------------------------------------
-- Combinators
-------------------------------------------------------------------------------

-- TODO: Reserved

-------------------------------------------------------------------------------
-- U
-------------------------------------------------------------------------------

data U = U !Int !ShortText deriving (Eq, Ord)

genU :: U -> Stream U
genU u@(U n t) = u :> genU (U (succ n) t)

freshU :: Set.Set U -> Stream U -> U
freshU xs (y :> ys)
    | Set.member y xs = freshU xs ys
    | otherwise       = y

toU :: ShortText -> U
toU t
    | null ds   = U 0 t
    | otherwise = U (read (reverse ds)) (T.pack (reverse rn))
  where
    (ds, rn) = span isDigit (reverse (T.unpack t))

fromU :: U -> String
fromU (U n t)
    | n <= 0    = T.unpack t
    | otherwise = T.unpack t ++ show n
  where

data Stream a = a :> Stream a

-------------------------------------------------------------------------------
-- Instances: base
-------------------------------------------------------------------------------

instance ToSyntax Void where
    toSyntax = absurd

-------------------------------------------------------------------------------
-- Instances: bound
-------------------------------------------------------------------------------

instance ToSyntax b => ToSyntax1 (Var b) where
    liftToSyntax s (F x) = s x
    liftToSyntax _ (B y) = toSyntax y

instance (ToSyntax b, ToSyntax a) => ToSyntax (Var b a) where
    toSyntax = toSyntax1

-------------------------------------------------------------------------------
-- Instances: unification-rigid
-------------------------------------------------------------------------------i

-- | TODO: introduce holes
instance ToSyntax MetaVar where
    toSyntax (MetaVar n) = return (fromString $ "?" ++ show n)

instance ToSyntax1 t => ToSyntax1 (UTerm t) where
    liftToSyntax s = go where
        go (UVar v)  = s v
        go (UTerm t) = liftToSyntax go t

instance (ToSyntax1 t, ToSyntax v) => ToSyntax (UTerm t v) where
    toSyntax = toSyntax1
