module OL1.Syntax.Type (
    Syntax (..),
    ) where

import Data.String                  (IsString (..))
import Math.NumberTheory.Logarithms (intLog2)

import qualified Test.QuickCheck as QC

import OL1.Syntax.Reserved
import OL1.Syntax.Sym

data Syntax
    = SSym Sym
    | SAt Syntax
    | SList [Syntax]
    | SRList Reserved [Syntax]
  deriving (Eq, Show)

instance IsString Syntax where
    fromString = SSym . fromString

instance QC.Arbitrary Syntax where
    arbitrary = QC.sized $ \n ->
        if n <= 0
        then QC.oneof
            [ SSym <$> QC.arbitrary
            , SAt . SSym <$> QC.arbitrary
            , pure (SList [])
            ]
        else QC.oneof
            [ SSym <$> QC.arbitrary
            , SList <$> QC.listOf (QC.scale intLog2 QC.arbitrary)
            , SRList <$> QC.arbitrary <*> QC.listOf (QC.scale intLog2 QC.arbitrary)
            ]


    shrink (SSym s)      = SSym <$> QC.shrink s
    shrink (SAt s)       = s : map SAt (QC.shrink s)
    shrink (SList xs)    = xs ++ map SList (QC.shrink xs)
    shrink (SRList r xs) = xs ++ map (SRList r) (QC.shrink xs)
