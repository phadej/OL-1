module OL1.Syntax.Pretty (
    syntaxToString,
    prettySyntax,
    ) where

import qualified Data.Text.Short          as T
import qualified Text.PrettyPrint.Compact as PP

import OL1.Syntax.Sym
import OL1.Syntax.Type

syntaxToString :: Syntax -> String
syntaxToString = PP.render . prettySyntax

prettySyntax :: Syntax -> PP.Doc ()
prettySyntax (SSym (Sym t)) = PP.text (T.unpack t)
prettySyntax (SList [])     = PP.text "()"
prettySyntax (SList (x:xs)) = PP.parens $ PP.hang 2 (prettySyntax x) (PP.sep (map prettySyntax xs))
