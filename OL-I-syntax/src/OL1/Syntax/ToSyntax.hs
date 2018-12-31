{-# LANGUAGE OverloadedStrings #-}
module OL1.Syntax.ToSyntax where

import Bound.Var                  (Var (..))
import Control.Applicative        (liftA2)
import Control.Monad.State.Strict (State, evalState, get, put)
import Control.Unification.Rigid  (MetaVar (..), UTerm (..))
import Data.Char                  (isDigit)
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

type SyntaxM = Printer SyntaxI

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
    toSyntax :: a -> Printer SyntaxI

class ToSyntax1 f where
    liftToSyntax :: (a -> Printer SyntaxI) -> f a -> Printer SyntaxI

instance ToSyntax Sym where
    toSyntax = return . SSym

instance ToSyntax (NSym n) where
    toSyntax (NSym _ s) = toSyntax s

instance ToSyntax a => ToSyntax (Irr a) where
    toSyntax (Irr a) = toSyntax a

instance f ~ I => ToSyntax (Syntax f) where
    toSyntax = return

instance ToSyntax a => ToSyntax (Printer a) where
    toSyntax = (>>= toSyntax)

toSyntax' :: ToSyntax a => a -> SyntaxI
toSyntax' = runPrinter . toSyntax

toSyntax1' :: (ToSyntax1 f, ToSyntax a) => f a -> SyntaxI
toSyntax1' = runPrinter . toSyntax1

toSyntax1 :: (ToSyntax1 f, ToSyntax a) => f a -> Printer SyntaxI
toSyntax1 = liftToSyntax toSyntax

-------------------------------------------------------------------------------
-- Freshen
-------------------------------------------------------------------------------

-- | Make fresh symbol variant.
freshen :: Sym -> (Sym -> Printer a) -> Printer a
freshen s f = freshenMany (I s) (f . unI)

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
sat = fmap sat'

sat' :: SyntaxI -> SyntaxI
sat' = SAt . I

ssym :: Sym -> SyntaxM
ssym = return . SSym

slist ::[SyntaxM] -> SyntaxM
slist = fmap slist' . sequenceA

slist' :: [SyntaxI] -> SyntaxI
slist' = SList . map I

srlist :: Reserved -> [SyntaxM] -> SyntaxM
srlist r = fmap (srlist' r) . sequenceA

srlist' :: Reserved -> [SyntaxI] -> SyntaxI
srlist' r = SRList (I r) . map I

-------------------------------------------------------------------------------
-- Higher order
-------------------------------------------------------------------------------

sthe :: SyntaxM -> SyntaxM -> SyntaxM
sthe = liftA2 impl where
    impl t x = srlist' RThe [t, x]

sarrow :: SyntaxM -> SyntaxM -> SyntaxM
sarrow = liftA2 arrow where
    arrow a (SRList (I RFnType) b) = srlist' RFnType (a : map unI b)
    arrow a b                      = srlist' RFnType [a, b]

sforall :: SyntaxM -> SyntaxM -> SyntaxM
sforall = liftA2 forall where
    forall a (SRList (I RFnType) b) = srlist' RFnType (sat' a : map unI b)
    forall a b                      = srlist' RFnType [sat' a, b]

sapp :: SyntaxM -> SyntaxM -> SyntaxM
sapp = liftA2 apply where
    apply (SList f) x = slist' (snoc (map unI f) x)
    apply f x         = slist' [f, x]

sappTy :: SyntaxM -> SyntaxM -> SyntaxM
sappTy = liftA2 apply where
    apply (SList f) x = slist' (snoc (map unI f) (sat' x))
    apply f x        = slist' [f, sat' x]

sfn :: SyntaxM -> SyntaxM -> SyntaxM
sfn = liftA2 impl where
    impl x (SRList (I RFn) [I (SList xs), I b]) = srlist' RFn [slist' (x : map unI xs), b]
    impl x b                                    = srlist' RFn [slist' [x], b]

spoly :: SyntaxM -> SyntaxM -> SyntaxM
spoly = liftA2 impl where
    impl x (SRList (I RFn) [I (SList xs) , I b]) = srlist' RFn [slist' (sat' x : map unI xs), b]
    impl x b                                     = srlist' RFn [slist' [sat' x], b]

stuple :: [SyntaxM] -> SyntaxM
stuple = srlist RTuple

scase :: SyntaxM -> [SyntaxM] -> SyntaxM -> SyntaxM
scase x xs y = srlist RSplit [x, slist xs, y]

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
