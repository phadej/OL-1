module OL1.Syntax (
    -- * Types
    Sym,
    ISym,
    NSym (..),
    Irr (..),
    Reserved (..),
    reservedToString,
    Syntax (..),
    hoistSyntax,
    SyntaxI,
    SyntaxS,
    -- * Re-exports
    Span, Spanned (..), I (..), unI,
    spannedToI,
    -- * Parsing
    syntaxFromString,
    parseSyntax,
    parseSyntaxes,
    -- * Pretty-printing
    syntaxToString,
    prettySyntax,
    -- * ToSyntax
    ToSyntax (..),
    ToSyntax1 (..),
    toSyntax',
    toSyntax1',
    Printer,
    runPrinter,
    SyntaxM,
    -- ** Low-level combinators
    ssym,
    sat,
    slist,
    srlist,
    freshen,
    freshenMany,
    freshenI,
    -- ** Higher-level combinators
    sthe,
    sarrow,
    sforall,
    sapp,
    sappTy,
    sfn,
    spoly,
    stuple,
    scase,
    -- * FromSyntax
    FromSyntax (..),
    runParser,
    Parser,
    failure,
    failFixit,
    ) where

import OL1.Syntax.FromSyntax
import OL1.Syntax.Parser
import OL1.Syntax.Pretty
import OL1.Syntax.Reserved
import OL1.Syntax.Sym
import OL1.Syntax.ToSyntax
import OL1.Syntax.Type

import Text.Trifecta (Span, Spanned (..))

spannedToI :: Spanned x -> I x
spannedToI (x :~ _) = I x
