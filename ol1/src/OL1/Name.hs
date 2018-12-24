module  OL1.Name where

import Data.Text (Text)

import OL1.Pretty

-- | Name, 'N'.
newtype N = N Text
  deriving Show

instance Eq N where
    _ == _  = True

instance Pretty N where
    ppr (N n) = ppr n
