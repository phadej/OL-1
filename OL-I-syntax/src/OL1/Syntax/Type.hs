{-# LANGUAGE UndecidableInstances #-}
module OL1.Syntax.Type (
    Syntax (..),
    hoistSyntax,
    SyntaxI,
    SyntaxS,
    I (..), unI,
    ) where

import Data.SOP.BasicFunctors       (I (..), unI)
import Data.String                  (IsString (..))
import Math.NumberTheory.Logarithms (intLog2)
import Text.Trifecta                (Spanned)

import qualified Test.QuickCheck as QC

import OL1.Syntax.Reserved
import OL1.Syntax.Sym

data Syntax f
    = SSym   Sym
    | SAt    (f (Syntax f))
    | SList  [f (Syntax f)]
    | SRList (f Reserved) [f (Syntax f)]

deriving instance (Eq (f (Syntax f)), Eq (f [Syntax f]), Eq (f Reserved)) => Eq (Syntax f)
deriving instance (Show (f (Syntax f)), Show (f [Syntax f]), Show (f Reserved)) => Show (Syntax f)

type SyntaxI = Syntax I
type SyntaxS = Syntax Spanned

instance IsString (Syntax f) where
    fromString = SSym . fromString

hoistSyntax :: Functor g => (forall x . f x -> g x) -> Syntax f -> Syntax g
hoistSyntax nt = go where
    go (SSym s)     = SSym s
    go (SAt x)      = SAt (fmap go (nt x))
    go (SList x)    = SList (fmap (fmap go . nt) x)
    go (SRList x y) = SRList (nt x) (fmap (fmap go . nt) y)

arbitrarySyntax :: QC.Gen SyntaxI
arbitrarySyntax = QC.sized $ \n ->
        if n <= 0
        then QC.oneof
            [ SSym <$> QC.arbitrary
            , SAt . I . SSym  <$> QC.arbitrary
            , pure (SList [])
            ]
        else QC.oneof
            [ SSym <$> QC.arbitrary
            , SAt . I . SSym  <$> QC.arbitrary
            , SList . map I <$> QC.listOf (QC.scale intLog2 arbitrarySyntax)
            , (\r s -> SRList (I r) (map I s))
                  <$> QC.arbitrary
                  <*> QC.listOf (QC.scale intLog2 arbitrarySyntax)
            ]

instance a ~ I => QC.Arbitrary (Syntax a) where
    arbitrary = arbitrarySyntax

    shrink (SSym s)    = SSym <$> QC.shrink s
    shrink (SAt (I s)) = s : map (SAt . I) (QC.shrink s)
    shrink (SList xs)  =
        let xs' = map unI xs
        in xs' ++ map (SList . map I) (QC.shrink xs')
    shrink (SRList r xs) =
        let xs' = map unI xs
        in xs' ++ map (SRList r . map I) (QC.shrink xs')
