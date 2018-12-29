module OL1.Syntax.Sym where

import Data.Char       (isPrint, isSeparator)
import Data.String     (IsString (..))
import Data.Text.Short (ShortText)
import Data.Fin (Fin)

import qualified Data.Text.Short as T
import qualified Test.QuickCheck as QC

newtype Sym = Sym ShortText
  deriving (Eq, Ord, Show)

isSymChar :: Char -> Bool
isSymChar c = isPrint c && c `notElem` "()[]{}@;" && not (isSeparator c)

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

newtype Irr a = Irr a
  deriving (Show)

instance IsString a => IsString (Irr a) where
    fromString = Irr . fromString

instance Eq (Irr a) where
    _ == _ = True

instance Ord (Irr a) where
    compare _ _ = EQ

-- | Irrelevant symbol, are all equal
type ISym = Irr Sym

data NSym n = NSym (Fin n) Sym
  deriving Show

instance Eq (NSym n) where
    NSym n _ == NSym n' _ = n == n'

instance Ord (NSym n) where
    compare (NSym n _) (NSym n' _) = compare n n'
