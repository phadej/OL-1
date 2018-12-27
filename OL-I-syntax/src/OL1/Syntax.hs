module OL1.Syntax (
    -- * Types
    Sym,
    ISym,
    Reserved (..),
    Syntax (..),
    -- * Parsing
    syntaxFromString,
    parseSyntax,
    parseSyntaxes,
    -- * Pretty-printing
    syntaxToString,
    prettySyntax,
    -- * ToSyntax
    ToSyntax (..),
    Printer,
    runPrinter,
    -- ** Low-level combinators
    ssym,
    sat,
    slist,
    srlist,
    freshen,
    freshenI,
    -- ** Higher-level combinators
    sthe,
    sarrow,
    sforall,
    sapp,
    sappTy,
    sfn,
    spoly,
    -- * FromSyntax
    FromSyntax (..),
    runParser,
    Parser,
    failure,
    ) where

import OL1.Syntax.FromSyntax
import OL1.Syntax.Parser
import OL1.Syntax.Pretty
import OL1.Syntax.Reserved
import OL1.Syntax.Sym
import OL1.Syntax.ToSyntax
import OL1.Syntax.Type
