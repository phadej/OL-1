module OL1.Pretty (
    Doc,
    MDoc,
    PrettyM,
    pretty,
    prettyPut,
    -- * Classes
    Pretty (..),
    Pretty1 (..),
    ppr1,
    -- * Combinators
    sexpr,
    (<+>), (</>), ($$$),
    tracePretty,
    pprIntegral,
    pprText,
    pprChar,
    -- * Fresh names
    pprScoped, pprScopedC,

    ) where

import Bound.Scope.Simple         (Scope (..))
import Bound.ScopeH               (ScopeH (..))
import Bound.ScopeT               (ScopeT (..))
import Bound.Var                  (Var (..))
import Control.Applicative        (liftA2)
import Control.Monad.State.Strict
import Control.Unification.Rigid  (MetaVar (..), UTerm (..))
import Data.Char                  (isDigit)
import Data.Coerce                (Coercible, coerce)
import Data.String                (IsString (..))
import Data.Text                  (Text)
import Data.Void                  (Void, absurd)
import Debug.Trace                (trace)

import qualified Data.Set                 as Set
import qualified Data.Text                as T
import qualified Text.PrettyPrint.Compact as PP

-------------------------------------------------------------------------------
-- Aliases
-------------------------------------------------------------------------------

type Doc = PP.Doc ()
type MDoc = PrettyM Doc

-------------------------------------------------------------------------------
-- Monad
-------------------------------------------------------------------------------

-- | State of pretty-printer's "used" symbols
type S = Set.Set U

-- | A pretty-printing monad, keeping state of binded symbols.
newtype PrettyM a = PrettyM { unPrettyM :: State S a }
  deriving newtype (Functor, Applicative, Monad)

runPrettyM :: PrettyM a -> a
runPrettyM (PrettyM m) = evalState m reserved

instance a ~ Doc => IsString (PrettyM a) where
    fromString = return . PP.text

instance a ~ Doc => Semigroup (PrettyM a) where
    (<>) = liftA2 (<>)

instance a ~ Doc => Monoid (PrettyM a) where
    mempty  = pure mempty
    mappend = (<>)

-------------------------------------------------------------------------------
-- Reserved words
-------------------------------------------------------------------------------

data Reserved
    = RForall
    | RArrow
    | RFun
    | RPoly
  deriving (Eq, Ord, Enum, Bounded)

reservedText :: Reserved -> String
reservedText RForall = "forall"
reservedText RArrow  = "->"
reservedText RFun    = "fn"
reservedText RPoly   = "poly"

reserved :: Set.Set U
reserved = Set.fromList [ U 0 $ T.pack $ reservedText r | r <- [ minBound .. maxBound ] ]

-------------------------------------------------------------------------------
-- U
-------------------------------------------------------------------------------

data U = U !Int !Text deriving (Eq, Ord)

genU :: U -> Stream U
genU u@(U n t) = u :> genU (U (succ n) t)

freshU :: Set.Set U -> Stream U -> U
freshU xs (y :> ys)
    | Set.member y xs = freshU xs ys
    | otherwise       = y

toU :: Text -> U
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
-- Classes
-------------------------------------------------------------------------------

class Pretty a where
    ppr :: a -> MDoc

class Pretty1 f where
    liftPpr :: (a -> MDoc) -> f a -> MDoc

instance a ~ () => Pretty (PP.Doc a) where
    ppr = return

instance a ~ Doc => Pretty (PrettyM a) where
    ppr = id

ppr1 :: (Pretty1 f, Pretty a) => f a -> MDoc
ppr1 = liftPpr ppr

-------------------------------------------------------------------------------
-- Functions
-------------------------------------------------------------------------------

pretty :: Pretty a => a -> String
pretty = PP.render . runPrettyM . ppr

prettyPut :: Pretty a => a -> IO ()
prettyPut = putStrLn . pretty

sexpr :: MDoc -> [MDoc] -> MDoc
sexpr f [] = PP.parens <$> f
sexpr f xs = mk <$> f <*> sequenceA xs where
    mk f' xs' = PP.parens $ PP.hang 2 f' (PP.sep xs')

tracePretty :: Pretty a => String -> a -> b -> b
tracePretty tag x = trace (pretty $ pprText tag </> ppr x)

-------------------------------------------------------------------------------
-- Combinators
-------------------------------------------------------------------------------

pprChar :: Char -> PrettyM Doc
pprChar = return . PP.char

pprText :: String -> PrettyM Doc
pprText = return . PP.text

pprIntegral :: Integral a => a -> PrettyM Doc
pprIntegral = return . PP.integer . fromIntegral

infixr 6 <+>
infixr 5 $$$, </>

(<+>) :: PrettyM Doc -> PrettyM Doc -> PrettyM Doc
(<+>) = liftA2 (PP.<+>)

(</>) :: PrettyM Doc -> PrettyM Doc -> PrettyM Doc
(</>) = liftA2 (PP.</>)

($$$) :: PrettyM Doc -> PrettyM Doc -> PrettyM Doc
($$$) = liftA2 (PP.$$)

-------------------------------------------------------------------------------
-- Instances
-------------------------------------------------------------------------------

instance Pretty () where
    ppr () = pprChar '?'

instance (Pretty a, Pretty b) => Pretty (a, b) where
    ppr (a, b) = sexpr (pprText "pair") [ppr a, ppr b]

instance (Pretty a, Pretty b, Pretty c) => Pretty (a, b, c) where
    ppr (a, b, c) = sexpr (pprText "triple") [ppr a, ppr b, ppr c]

instance Pretty a => Pretty (Maybe a) where
    ppr = maybe (pprChar '?') ppr

instance Pretty a => Pretty [a] where
    ppr [] = pprText "[]"
    ppr xs = PP.brackets . PP.sep <$> traverse ppr xs

instance Pretty Void where
    ppr = absurd

instance Pretty Text where
    ppr = pprText . T.unpack

instance Pretty b => Pretty1 (Either b) where
    liftPpr pp (Right x) = pp x
    liftPpr _  (Left y)  = ppr y

instance (Pretty b, Pretty a) => Pretty (Either a b) where ppr = ppr1

-------------------------------------------------------------------------------
-- Bound
-------------------------------------------------------------------------------

instance Pretty b => Pretty1 (Var b) where
    liftPpr pp (F x) = pp x
    liftPpr _  (B y) = ppr y

instance (Pretty b, Pretty a) => Pretty (Var a b) where ppr = ppr1

instance (Pretty b, Pretty1 (t f), Pretty1 f) => Pretty1 (ScopeT b t f) where
    liftPpr pp (ScopeT s) = liftPpr (liftPpr (liftPpr pp)) s

instance (Pretty b, Pretty1 f, Pretty1 m) => Pretty1 (ScopeH b f m) where
    liftPpr pp (ScopeH s) = liftPpr (liftPpr (liftPpr pp)) s

instance (Pretty n, Pretty1 f) => Pretty1 (Scope n f) where
    liftPpr pp (Scope s) = liftPpr (liftPpr pp) s

-------------------------------------------------------------------------------
-- Scoped
-------------------------------------------------------------------------------

pprScoped :: Text -> (Doc -> PrettyM a) -> PrettyM a
pprScoped s f
    | s == T.pack "_" = f (PP.char '_')
    | otherwise = PrettyM $ do
        xs <- get
        let u = freshU xs (genU (toU s))
        put (Set.insert u xs)
        x <- unPrettyM (f (PP.text (fromU u)))
        modify' (Set.delete u)
        return x

pprScopedC :: Coercible Text s => s -> (Doc -> PrettyM a) -> PrettyM a
pprScopedC = pprScoped . coerce

-------------------------------------------------------------------------------
-- OL1.Unify
-------------------------------------------------------------------------------

instance Pretty MetaVar where
    ppr (MetaVar n) = pprChar '?' <> pprIntegral (n + minBound)

instance Pretty1 t => Pretty1 (UTerm t) where
    liftPpr pp = go where
        go (UVar v)  = pp v
        go (UTerm t) = liftPpr go t

instance (Pretty1 t, Pretty a) => Pretty (UTerm t a) where ppr = ppr1
