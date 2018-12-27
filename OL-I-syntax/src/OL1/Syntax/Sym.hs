module OL1.Syntax.Sym where

import Data.Char       (isPrint, isSeparator)
import Data.String     (IsString (..))
import Data.Text.Short (ShortText)

import qualified Data.Text.Short as T
import qualified Test.QuickCheck as QC

newtype Sym = Sym ShortText
  deriving (Eq, Ord, Show)

isSymChar :: Char -> Bool
isSymChar c = isPrint c && c `notElem` "()[]{}@" && not (isSeparator c)

instance IsString Sym where
    fromString = Sym . fromString

instance QC.Arbitrary Sym where
    arbitrary = QC.frequency
        [ (10, fromString <$> QC.listOf1 (QC.elements ['a'..'z']))
        , (1, fromString <$> QC.listOf1 arbChar)
        ]
      where
        arbChar = QC.arbitrary `QC.suchThat` isSymChar

    shrink (Sym s) = case T.unpack s of
        []     -> []
        (x:xs) ->
            [ Sym (T.pack ys)
            | x' <- QC.shrink x
            , xs' <- QC.shrink xs
            , let ys = filter isSymChar (x' : xs')
            , not (null ys)
            ]

-- | Irrelevant symbol, are all equal
newtype ISym = ISym Sym 
  deriving (Show)

instance IsString ISym where
    fromString = ISym . fromString

instance Eq ISym where
    _ == _ = True

instance Ord ISym where
    compare _ _ = EQ
