module OL1.Syntax (
    -- * Types
    Sym,
    ISym,
    Reserved (..),
    Syntax (..),
    AppSyntax (..),
    -- * Parsing
    syntaxFromString,
    parseSyntax,
    parseSyntaxes,
    -- * Pretty-printing
    syntaxToString,
    prettySyntax,
    ) where

import OL1.Syntax.Parser
import OL1.Syntax.Pretty
import OL1.Syntax.Reserved
import OL1.Syntax.Sym
import OL1.Syntax.Type
