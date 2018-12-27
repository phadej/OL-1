module OL1.Syntax.FromSyntax where

import Prelude ()
import Prelude.Compat

import Control.Applicative (Alternative (..))
import Control.Monad       (MonadPlus (..))

import OL1.Syntax.Sym
import OL1.Syntax.Type

-------------------------------------------------------------------------------
-- Types
-------------------------------------------------------------------------------

newtype Parser a = Parser { runParser :: Either String a }
  deriving newtype (Functor, Applicative, Monad)

failure :: String -> Parser a
failure = Parser . Left

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
    fromSyntax :: Syntax -> Parser a

instance FromSyntax Sym where
    fromSyntax (SSym s) = return s
    fromSyntax _        = failure "not sym"

instance FromSyntax Syntax where
    fromSyntax = return

-------------------------------------------------------------------------------
-- Combinators
-------------------------------------------------------------------------------

eitherFromSyntax :: (FromSyntax a, FromSyntax b) => Syntax -> Either String (Either a b)
eitherFromSyntax s = runParser $
    Left <$> fromSyntax s <|> Right <$> fromSyntax s
