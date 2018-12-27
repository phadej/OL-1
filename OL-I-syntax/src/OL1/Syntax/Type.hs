module OL1.Syntax.Type (
    Syntax (..),
    AppSyntax (..),
    ) where

import Data.String                  (IsString (..))
import Math.NumberTheory.Logarithms (intLog2)

import qualified Test.QuickCheck as QC

import OL1.Syntax.Reserved
import OL1.Syntax.Sym

data Syntax
    = SSym Sym
    | SNil -- combine this and next
    | SList Syntax [AppSyntax]
    | SRList Reserved [AppSyntax]
  deriving (Eq, Show)

data AppSyntax
    = Juxta Syntax
    | At Syntax
  deriving (Eq, Show)

instance IsString Syntax where
    fromString = SSym . fromString

instance QC.Arbitrary AppSyntax where
    arbitrary = QC.oneof
        [ Juxta <$> QC.arbitrary
        , At <$> QC.arbitrary
        ]

instance QC.Arbitrary Syntax where
    arbitrary = QC.sized $ \n ->
        if n <= 0
        then QC.oneof
            [ SSym <$> QC.arbitrary
            , pure SNil 
            ]
        else QC.oneof
            [ SSym <$> QC.arbitrary
            , pure SNil
            , SList <$> QC.scale intLog2 QC.arbitrary <*> QC.listOf (QC.scale intLog2 QC.arbitrary)
            , SRList <$> QC.arbitrary <*> QC.listOf (QC.scale intLog2 QC.arbitrary)
            ]


    shrink (SSym s)      = SSym <$> QC.shrink s
    shrink SNil          = []
    shrink (SList x xs)  = SNil : x : map unAppSyntax xs
    shrink (SRList _ xs) = SNil : map unAppSyntax xs

unAppSyntax :: AppSyntax -> Syntax
unAppSyntax (Juxta s) = s
unAppSyntax (At s)    = s
