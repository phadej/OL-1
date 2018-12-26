module OL1.Syntax.Reserved where

import qualified Test.QuickCheck as QC

data Reserved
    = RThe    -- ^ @the@
    | RFnType -- ^ @fn-type@
    | RFn     -- ^ @fn@
    | RPoly   -- ^ @poly@
  deriving (Eq, Ord, Show, Enum, Bounded)

reservedToString :: Reserved -> String
reservedToString RThe    = "the"
reservedToString RFn     = "fn"
reservedToString RPoly   = "poly"
reservedToString RFnType = "fn-type"

instance QC.Arbitrary Reserved where
    arbitrary = QC.arbitraryBoundedEnum
