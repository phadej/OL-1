module OL1.Syntax.Reserved where

import qualified Test.QuickCheck as QC

data Reserved
    = RThe    -- ^ @the@
    | RFnType -- ^ @fn-type@
    | RFn     -- ^ @fn@

    | RTuple  -- ^ @tuple@
    | RSplit  -- ^ @split@

    | REnum   -- ^ @enum@
    | RMatch  -- ^ @match@

  deriving (Eq, Ord, Show, Enum, Bounded)

reservedToString :: Reserved -> String
reservedToString RThe    = "the"
reservedToString RFn     = "fn"
reservedToString RFnType = "->"

reservedToString RTuple = "tuple"
reservedToString RSplit = "split"

reservedToString REnum  = "enum"
reservedToString RMatch = "match"

instance QC.Arbitrary Reserved where
    arbitrary = QC.arbitraryBoundedEnum
