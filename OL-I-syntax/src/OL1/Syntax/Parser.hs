module OL1.Syntax.Parser (
    syntaxFromString,
    parseSyntax,
    parseSyntaxes,
    ) where

import Control.Applicative (Alternative (..))
import Data.String         (fromString)
import Data.Char (isSpace)
import Text.Trifecta
       (CharParsing, skipSome, manyTill, Parser, Parsing, Result (..), TokenParsing (..), char,
       choice, eof, highlight, parens, parseByteString, satisfy, string, token,
       whiteSpace, _errDoc)
import Text.Trifecta.Delta (Delta (Directed))

import qualified Data.ByteString              as BS
import qualified Data.ByteString.UTF8         as UTF8
import qualified Text.Parser.Token.Highlight  as H
import qualified Text.PrettyPrint.ANSI.Leijen as A

import OL1.Syntax.Reserved
import OL1.Syntax.Sym
import OL1.Syntax.Type

syntaxFromString :: String -> Either String Syntax
syntaxFromString = parseSyntax "<input>" . UTF8.fromString

parseSyntax :: FilePath -> BS.ByteString -> Either String Syntax
parseSyntax fp bs =
    case parseByteString (runP $ whiteSpace *> syntaxP <* eof) (Directed (UTF8.fromString fp) 0 0 0 0) bs of
        Success sy  -> Right sy
        Failure err -> Left $ show' $ _errDoc err

show' :: A.Doc -> String
show' doc = A.displayS (stripSGR $ A.renderPretty 0.4 80 doc) ""

stripSGR :: A.SimpleDoc -> A.SimpleDoc
stripSGR A.SFail         = A.SFail
stripSGR A.SEmpty        = A.SEmpty
stripSGR (A.SChar x d)   = A.SChar x (stripSGR d)
stripSGR (A.SText i x d) = A.SText i x (stripSGR d)
stripSGR (A.SLine i d)   = A.SLine i (stripSGR d)
stripSGR (A.SSGR _ d)    = stripSGR d

parseSyntaxes :: FilePath -> BS.ByteString -> Either String [Syntax]
parseSyntaxes fp bs =
    case parseByteString (runP $ whiteSpace *> many syntaxP <* eof) (Directed (UTF8.fromString fp) 0 0 0 0) bs of
        Success sy  -> Right sy
        Failure err -> Left $ show' $ _errDoc err

syntaxP :: P Syntax
syntaxP = choice
    [ SSym <$> symP
    , char '@' *> (SAt <$> syntaxP)
    , parens (listP <|> pure (SList []))
    ]
  where
    listP :: P Syntax
    listP = (SRList <$> reservedP <|> pure SList) <*> many syntaxP

reservedP :: P Reserved
reservedP = choice
    [ token $ highlight H.ReservedIdentifier $ r <$ string (reservedToString r)
    | r <- [ minBound .. maxBound ]
    ]

symP :: P Sym
symP = token $ highlight H.Symbol $ fromString <$> some symCharP where
    symCharP = satisfy isSymChar

newtype P a = P { runP :: Parser a }
  deriving newtype (Functor, Applicative, Alternative, Parsing, CharParsing)

instance TokenParsing P where
    someSpace = P $ skipSome $ satisfy isSpace <|> commentP

    nesting     = P . nesting . runP
    highlight h = P . highlight h . runP

commentP :: Parser Char
commentP = char ';' <* manyTill (satisfy (/= '\n')) (char '\n')
