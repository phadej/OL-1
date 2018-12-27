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
    -- * ToSyntax
    ToSyntax (..),
    runPrinter,
    -- ** Low-level combinators
    ssym,
    slist,
    slist',
    srlist,
    srlist',
    freshen,
    -- * FromSyntax
    FromSyntax (..),
    runParser,
    -- * Sugar
    desugar,
    ) where

import OL1.Syntax.FromSyntax
import OL1.Syntax.Parser
import OL1.Syntax.Pretty
import OL1.Syntax.Reserved
import OL1.Syntax.Sym
import OL1.Syntax.Sugar
import OL1.Syntax.ToSyntax
import OL1.Syntax.Type
