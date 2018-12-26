module OL1.Syntax.Parser (
    syntaxFromString,
    parseSyntax,
    parseSyntaxes,
    ) where

import Control.Applicative (many, some, (<|>))
import Data.String         (fromString)
import Text.Trifecta
       (Parser, Result (..), eof, highlight, choice, parens, parseByteString, satisfy,
       token, whiteSpace, _errDoc, char, string)
import Text.Trifecta.Delta (Delta (Directed))

import qualified Data.ByteString             as BS
import qualified Data.ByteString.UTF8        as UTF8
import qualified Text.Parser.Token.Highlight as H

import OL1.Syntax.Sym
import OL1.Syntax.Reserved
import OL1.Syntax.Type

syntaxFromString :: String -> Either String Syntax
syntaxFromString = parseSyntax "<input>" . UTF8.fromString

parseSyntax :: FilePath -> BS.ByteString -> Either String Syntax
parseSyntax fp bs =
    case parseByteString (whiteSpace *> syntaxP <* eof) (Directed (UTF8.fromString fp) 0 0 0 0) bs of
        Success sy  -> Right sy
        Failure err -> Left $ show $ _errDoc err

parseSyntaxes :: FilePath -> BS.ByteString -> Either String [Syntax]
parseSyntaxes fp bs =
    case parseByteString (whiteSpace *> many syntaxP <* eof) (Directed (UTF8.fromString fp) 0 0 0 0) bs of
        Success sy  -> Right sy
        Failure err -> Left $ show $ _errDoc err

syntaxP :: Parser Syntax
syntaxP = SSym <$> symP <|> parens (listP <|> pure SNil)
  where
    listP :: Parser Syntax
    listP = (SRList <$> reservedP <|> SList <$> syntaxP) <*> many appSyntaxP

reservedP :: Parser Reserved
reservedP = choice
    [ token $ highlight H.ReservedIdentifier $ r <$ string (reservedToString r)
    | r <- [ minBound .. maxBound ]
    ]

appSyntaxP :: Parser AppSyntax
appSyntaxP = At <$ char '@' <*> syntaxP <|> Juxta <$> syntaxP

symP :: Parser Sym
symP = token $ highlight H.Symbol $ fromString <$> some symCharP where
    symCharP = satisfy isSymChar
