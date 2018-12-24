module OL1.Syntax.Sym where

import Data.String     (IsString (..))
import Data.Text.Short (ShortText)
import Test.QuickCheck (Arbitrary (..), suchThat, liftArbitrary)
import Data.Char (isPrint, isSeparator)

import qualified Data.Text.Short as T

newtype Sym = Sym ShortText
  deriving (Eq, Ord, Show)

isSymChar :: Char -> Bool
isSymChar c = isPrint c && c `notElem` "()[]{}" && not (isSeparator c)

instance IsString Sym where
    fromString = Sym . fromString

instance Arbitrary Sym where
    arbitrary = mk <$> arbChar <*> liftArbitrary arbChar where
        mk x xs = Sym $ T.pack $ x : xs

        arbChar = arbitrary `suchThat` isSymChar

    shrink (Sym s) = case T.unpack s of
        []     -> []
        (x:xs) ->
            [ Sym (T.pack ys)
            | x' <- shrink x
            , xs' <- shrink xs
            , let ys = filter isSymChar (x' : xs')
            , not (null ys)
            ]

-- | Irrelevant symbol, are all equal
newtype ISym = ISym ShortText
  deriving (Show)

instance IsString ISym where
    fromString = ISym . fromString

instance Eq ISym where
    _ == _ = True

instance Ord ISym where
    compare _ _ = EQ
