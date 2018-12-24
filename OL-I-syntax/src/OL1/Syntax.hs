module OL1.Syntax (
    -- * Types
    Sym,
    ISym,
    Syntax (..),
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
import OL1.Syntax.Sym
import OL1.Syntax.Type
