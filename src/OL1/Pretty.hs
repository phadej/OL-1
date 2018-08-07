-- | TODO: Add context for renaming?
module OL1.Pretty where

import Bound.Scope.Simple (Scope (..))
import Bound.ScopeH       (ScopeH (..))
import Bound.ScopeT       (ScopeT (..))
import Bound.Var          (Var (..))
import Data.Text          (Text)
import Data.Void          (Void, absurd)
import Debug.Trace        (trace)

import qualified Control.Unification        as U
import qualified Control.Unification.IntVar as U
import qualified Data.Text                  as T
import qualified Text.PrettyPrint.Compact   as PP

type Doc = PP.Doc ()

class Pretty a where
    ppr :: a -> Doc

class Pretty1 f where
    liftPpr :: (a -> Doc) -> f a -> Doc

instance a ~ () => Pretty (PP.Doc a) where
    ppr = id

ppr1 :: (Pretty1 f, Pretty a) => f a -> Doc
ppr1 = liftPpr ppr

-------------------------------------------------------------------------------
-- Functions
-------------------------------------------------------------------------------

pretty :: Pretty a => a -> String
pretty = PP.render . ppr

prettyPut :: Pretty a => a -> IO ()
prettyPut = putStrLn . pretty

sexpr :: Doc -> [Doc] -> Doc
sexpr f [] = PP.parens f
sexpr f xs = PP.parens $ PP.hang 2 f (PP.sep xs)

tracePretty :: Pretty a => String -> a -> b -> b
tracePretty tag x = trace (PP.render $ PP.text tag PP.</> ppr x)

-------------------------------------------------------------------------------
-- Instances
-------------------------------------------------------------------------------

instance Pretty () where
    ppr () = PP.char '?'

instance (Pretty a, Pretty b) => Pretty (a, b) where
    ppr (a, b) = sexpr (PP.text "2-tuple") [ppr a, ppr b]

instance (Pretty a, Pretty b, Pretty c) => Pretty (a, b, c) where
    ppr (a, b, c) = sexpr (PP.text "3-tuple") [ppr a, ppr b, ppr c]

instance Pretty a => Pretty (Maybe a) where
    ppr = maybe (PP.char '?') ppr

instance Pretty a => Pretty [a] where
    ppr [] = PP.text "[]"
    ppr xs = PP.brackets $ PP.sep $ map ppr xs

instance Pretty Void where
    ppr = absurd

instance Pretty Text where
    ppr = PP.text . T.unpack

instance Pretty b => Pretty1 (Var b) where
    liftPpr pp (F x) = pp x
    liftPpr _  (B y) = ppr y

instance (Pretty b, Pretty a) => Pretty (Var a b) where ppr = ppr1

instance Pretty b => Pretty1 (Either b) where
    liftPpr pp (Right x) = pp x
    liftPpr _  (Left y)  = ppr y

instance (Pretty b, Pretty a) => Pretty (Either a b) where ppr = ppr1

instance (Pretty b, Pretty1 (t f), Pretty1 f) => Pretty1 (ScopeT b t f) where
    liftPpr pp (ScopeT s) = liftPpr (liftPpr (liftPpr pp)) s

instance (Pretty b, Pretty1 f, Pretty1 m) => Pretty1 (ScopeH b f m) where
    liftPpr pp (ScopeH s) = liftPpr (liftPpr (liftPpr pp)) s

instance (Pretty n, Pretty1 f) => Pretty1 (Scope n f) where
    liftPpr pp (Scope s) = liftPpr (liftPpr pp) s

instance Pretty U.IntVar where
    ppr (U.IntVar n) = PP.char '?' PP.<> PP.int (n + minBound)

instance Pretty1 t => Pretty1 (U.UTerm t) where
    liftPpr pp = go where
        go (U.UVar v)  = pp v
        go (U.UTerm t) = liftPpr go t

instance (Pretty1 t, Pretty a) => Pretty (U.UTerm t a) where ppr = ppr1
