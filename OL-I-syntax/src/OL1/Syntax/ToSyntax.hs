{-# LANGUAGE OverloadedStrings #-}
module OL1.Syntax.ToSyntax where

import Bound.Var                  (Var (..))
import Control.Applicative        (liftA2)
import Control.Monad.State.Strict (State, evalState, get, put)
import Control.Unification.Rigid  (MetaVar (..), UTerm (..))
import Data.Char                  (isDigit)
import Data.Functor.Identity      (Identity (..))
import Data.String                (IsString (..))
import Data.Text.Short            (ShortText)
import Data.Traversable           (for)
import Data.Void                  (Void, absurd)

import qualified Data.Set        as Set
import qualified Data.Text.Short as T

import OL1.Syntax.Reserved
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

instance ToSyntax (NSym n) where
    toSyntax (NSym _ s) = toSyntax s

instance ToSyntax a => ToSyntax (Irr a) where
    toSyntax (Irr a) = toSyntax a

instance ToSyntax Syntax where
    toSyntax = return

instance ToSyntax a => ToSyntax (Printer a) where
    toSyntax = (>>= toSyntax)

toSyntax' :: ToSyntax a => a -> Syntax
toSyntax' = runPrinter . toSyntax

toSyntax1' :: (ToSyntax1 f, ToSyntax a) => f a -> Syntax
toSyntax1' = runPrinter . toSyntax1

toSyntax1 :: (ToSyntax1 f, ToSyntax a) => f a -> SyntaxM
toSyntax1 = liftToSyntax toSyntax

-------------------------------------------------------------------------------
-- Freshen
-------------------------------------------------------------------------------

-- | Make fresh symbol variant.
freshen :: Sym -> (Sym -> Printer a) -> Printer a
freshen s f = freshenMany (Identity s) (f . runIdentity)

freshenMany :: Traversable t => t Sym -> (t Sym -> Printer a) -> Printer a
freshenMany ss f = Printer $ do
    xs <- get
    us <- for ss $ \(Sym s) -> do
        xs' <- get
        let u = freshU xs' (genU (toU s))
        put (Set.insert u xs)
        return (fromString (fromU u))

    x <- unPrinter (f us)
    put xs
    return x

freshenI :: ISym -> (Sym -> Printer a) -> Printer a
freshenI (Irr s) = freshen s

-------------------------------------------------------------------------------
-- Combinators
-------------------------------------------------------------------------------

sat :: SyntaxM -> SyntaxM
sat = fmap SAt

ssym :: Sym -> SyntaxM
ssym = return . SSym

slist ::[SyntaxM] -> SyntaxM
slist = fmap SList . sequenceA

srlist :: Reserved -> [SyntaxM] -> SyntaxM
srlist r = fmap (SRList r) . sequenceA

-------------------------------------------------------------------------------
-- Higher order
-------------------------------------------------------------------------------

sthe :: SyntaxM -> SyntaxM -> SyntaxM
sthe = liftA2 impl where
    impl t x = SRList RThe [t, x]

sarrow :: SyntaxM -> SyntaxM -> SyntaxM
sarrow = liftA2 arrow where
    arrow a (SRList RFnType b) = SRList RFnType (a : b)
    arrow a b                  = SRList RFnType [a, b]

sforall :: SyntaxM -> SyntaxM -> SyntaxM
sforall = liftA2 forall where
    forall a (SRList RFnType b) = SRList RFnType (SAt a : b)
    forall a b                  = SRList RFnType [SAt a, b]

sapp :: SyntaxM -> SyntaxM -> SyntaxM
sapp = liftA2 apply where
    apply (SList f) x = SList (snoc f x)
    apply f x         = SList [f, x]

sappTy :: SyntaxM -> SyntaxM -> SyntaxM
sappTy = liftA2 apply where
    apply (SList f) x = SList (snoc f (SAt x))
    apply f x         = SList [f, SAt x]

sfn :: SyntaxM -> SyntaxM -> SyntaxM
sfn = liftA2 impl where
    impl x (SRList RFn [SList xs, b]) = SRList RFn [SList (x:xs), b]
    impl x b                          = SRList RFn [SList [x], b]

spoly :: SyntaxM -> SyntaxM -> SyntaxM
spoly = liftA2 impl where
    impl x (SRList RFn [SList xs, b]) = SRList RFn [SList (SAt x:xs), b]
    impl x b                          = SRList RFn [SList [SAt x], b]

stuple :: [SyntaxM] -> SyntaxM
stuple = fmap (SRList RTuple) . sequenceA

scase :: SyntaxM -> [SyntaxM] -> SyntaxM -> SyntaxM
scase x xs y = impl <$> x <*> sequenceA xs <*> y where
    impl a b c = SRList RSplit [a, SList b, c]

snoc :: [a] -> a -> [a]
snoc xs x = xs ++ [x]

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

instance ToSyntax () where
    toSyntax _ = slist []

instance ToSyntax Void where
    toSyntax = absurd

instance ToSyntax1 Maybe where
    liftToSyntax s (Just x) = s x
    liftToSyntax _ Nothing  = ssym "?"

instance ToSyntax b => ToSyntax1 (Either b) where
    liftToSyntax s (Right x) = s x
    liftToSyntax _ (Left y) = toSyntax y

instance (ToSyntax a) => ToSyntax (Maybe a) where
    toSyntax = toSyntax1

instance (ToSyntax b, ToSyntax a) => ToSyntax (Either b a) where
    toSyntax = toSyntax1

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
    toSyntax (MetaVar n) = return (fromString $ "?" ++ show (n + minBound))

instance ToSyntax1 t => ToSyntax1 (UTerm t) where
    liftToSyntax s = go where
        go (UVar v)  = s v
        go (UTerm t) = liftToSyntax go t

instance (ToSyntax1 t, ToSyntax v) => ToSyntax (UTerm t v) where
    toSyntax = toSyntax1
