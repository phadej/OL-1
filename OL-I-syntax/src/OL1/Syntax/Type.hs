module OL1.Syntax.Type (
    Syntax (..)
    ) where

import Data.String     (IsString (..))
import Test.QuickCheck (Arbitrary (..))
import Math.NumberTheory.Logarithms (intLog2)
import Control.Monad (replicateM)

import qualified Test.QuickCheck as QC

import OL1.Syntax.Sym

data Syntax
    = SSym Sym
    | SList [Syntax]
  deriving (Eq, Show)

instance IsString Syntax where
    fromString = SSym . fromString

instance Arbitrary Syntax where
    arbitrary = QC.sized arb where
        arb n | n <= 0    = SSym <$> arbitrary
              | otherwise = QC.oneof
                  [ SSym <$> arbitrary
                  , do
                      let m = intLog2 n
                      p <- QC.choose (0, m)
                      SList <$> replicateM p (arb m)
                  ]

    shrink (SSym s)   = SSym <$> shrink s
    shrink (SList xs) = xs ++ map SList (shrink xs)
