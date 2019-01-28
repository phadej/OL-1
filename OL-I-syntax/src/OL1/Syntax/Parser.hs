module OL1.Syntax.Parser (
    syntaxFromString,
    parseSyntax,
    parseSyntaxes,
    ) where

import Control.Applicative (Alternative (..))
import Control.Monad       (MonadPlus)
import Data.Char           (isSpace)
import Data.String         (fromString)
import Text.Trifecta
       (CharParsing, DeltaParsing, Parser, Parsing, Result (..), Spanned (..),
       TokenParsing (..), char, choice, eof, highlight, manyTill,
        parens, notFollowedBy, parseByteString, satisfy, skipSome, spanned,
       string, token, whiteSpace, _errDoc, try)
import Text.Trifecta.Delta (Delta (Directed))

import qualified Data.ByteString             as BS
import qualified Data.ByteString.UTF8        as UTF8
import qualified Text.Parser.Token.Highlight as H

import OL1.Syntax.Internal
import OL1.Syntax.Reserved
import OL1.Syntax.Sym
import OL1.Syntax.Type

syntaxFromString :: String -> Either String (Spanned SyntaxS)
syntaxFromString = parseSyntax "<input>" . UTF8.fromString

parseSyntax :: FilePath -> BS.ByteString -> Either String (Spanned SyntaxS)
parseSyntax fp bs =
    case parseByteString (runP $ whiteSpace *> spanned syntaxP <* eof) (Directed (UTF8.fromString fp) 0 0 0 0) bs of
        Success sy  -> Right sy
        Failure err -> Left $ prettyShow $ _errDoc err

parseSyntaxes :: FilePath -> BS.ByteString -> Either String [Spanned SyntaxS]
parseSyntaxes fp bs =
    case parseByteString (runP $ whiteSpace *> many (spanned syntaxP) <* eof) (Directed (UTF8.fromString fp) 0 0 0 0) bs of
        Success sy  -> Right sy
        Failure err -> Left $ prettyShow $ _errDoc err

-------------------------------------------------------------------------------
-- Parsers
-------------------------------------------------------------------------------

syntaxP :: P SyntaxS
syntaxP = choice
    [ SSym <$> symP
    , char '@' *> (SAt <$> spanned syntaxP)
    , parens (listP <|> SList <$> pure [])
    ]
  where
    listP :: P SyntaxS
    listP = (SRList <$> spanned reservedP <|> pure SList) <*> many (spanned syntaxP)

reservedP :: P Reserved
reservedP = choice
    [ token $ highlight H.ReservedIdentifier $ try $ r <$ do
        s <- string (reservedToString r)
        notFollowedBy symCharP
        return s
    | r <- [ minBound .. maxBound ]
    ]

symP :: P Sym
symP = token $ highlight H.Symbol $ fromString <$> some symCharP where

symCharP :: P Char
symCharP = satisfy isSymChar

-------------------------------------------------------------------------------
-- Parser type
-------------------------------------------------------------------------------

newtype P a = P { runP :: Parser a }
  deriving newtype ( Functor, Applicative, Alternative, Monad, MonadPlus
                   , Parsing, CharParsing, DeltaParsing)

instance TokenParsing P where
    someSpace = P $ skipSome $ satisfy isSpace <|> commentP

    nesting     = P . nesting . runP
    highlight h = P . highlight h . runP

commentP :: Parser Char
commentP = char ';' <* manyTill (satisfy (/= '\n')) (char '\n')
