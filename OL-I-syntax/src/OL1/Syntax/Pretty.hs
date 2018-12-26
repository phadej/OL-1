module OL1.Syntax.Pretty (
    syntaxToString,
    prettySyntax,
    ) where

import qualified Data.Text.Short          as T
import qualified Text.PrettyPrint.Compact as PP

import OL1.Syntax.Reserved
import OL1.Syntax.Sym
import OL1.Syntax.Type

syntaxToString :: Syntax -> String
syntaxToString = PP.render . prettySyntax

prettySym :: Sym -> PP.Doc ()
prettySym (Sym t) = PP.text (T.unpack t)

prettyReserved :: Reserved -> PP.Doc ()
prettyReserved = PP.text . reservedToString

prettySyntax :: Syntax -> PP.Doc ()
prettySyntax (SSym s)      = prettySym s
prettySyntax SNil          = PP.text "()"
prettySyntax (SList x xs)  = PP.parens $ PP.hang 2 (prettySyntax x) (PP.sep (map prettyAppSyntax xs))
prettySyntax (SRList x xs) = PP.parens $ PP.hang 2 (prettyReserved x) (PP.sep (map prettyAppSyntax xs))

prettyAppSyntax :: AppSyntax -> PP.Doc ()
prettyAppSyntax (Juxta s) = prettySyntax s
prettyAppSyntax (At s)    = PP.char '@' <> prettySyntax s
