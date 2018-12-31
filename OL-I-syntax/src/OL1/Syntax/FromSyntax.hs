module OL1.Syntax.FromSyntax where

import Prelude ()
import Prelude.Compat hiding (span)

import Control.Applicative (Alternative (..))
import Control.Lens        ((^.))
import Control.Monad       (MonadPlus (..))
import Data.Bifunctor      (first)
import Text.Trifecta       (Spanned (..), render, Span, span)

import OL1.Syntax.Internal
import OL1.Syntax.Sym
import OL1.Syntax.Type

-------------------------------------------------------------------------------
-- Types
-------------------------------------------------------------------------------

newtype Parser a = Parser { runParser :: Either (Maybe Span, String) a }
  deriving newtype (Functor, Applicative, Monad)

failure :: String -> Parser a
failure err = Parser (Left (Nothing, err))

failFixit :: Span -> String -> Parser a
failFixit sp err = Parser (Left (Just sp, err))

instance Alternative Parser where
    empty = failure "empty"
    x@(Parser (Right _)) <|> _ = x
    (Parser (Left _))    <|> y = y

instance MonadPlus Parser where
    mzero = empty
    mplus = (<|>)

-------------------------------------------------------------------------------
-- Classes
-------------------------------------------------------------------------------

-- |
--
-- TODO: structured errors
class FromSyntax a where
    fromSyntax :: Spanned SyntaxS -> Parser a

instance FromSyntax Sym where
    fromSyntax (SSym s :~ _) = return s
    fromSyntax s             = failFixit (s ^. span) "Expecting symbol"

instance f ~ Spanned => FromSyntax (Syntax f) where
    fromSyntax (s :~ _) = return s

-------------------------------------------------------------------------------
-- Combinators
-------------------------------------------------------------------------------

eitherFromSyntax :: (FromSyntax a, FromSyntax b) => Spanned SyntaxS -> Either String (Either a b)
eitherFromSyntax s
    = first renderErr
    $ runParser
    $ Left <$> fromSyntax s <|> Right <$> fromSyntax s
  where
    renderErr (Nothing, err) = err
    renderErr (Just sp, err) = err ++ "\n" ++ prettyShow (render sp)
