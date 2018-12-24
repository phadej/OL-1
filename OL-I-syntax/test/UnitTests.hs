module Main (main) where

import Test.Tasty        (defaultMain, testGroup)
import Test.Tasty.QuickCheck (testProperty)
import Test.QuickCheck (counterexample, (===), Property)

import OL1.Syntax

main :: IO ()
main = defaultMain $ testGroup "Properties"
    [ testProperty "roundtrip" roundtripProp
    ]

roundtripProp :: Syntax -> Property
roundtripProp s = counterexample str $ case syntaxFromString str of
    Right s' -> counterexample (show s') $ s === s'
    Left err -> counterexample err False
  where
    str = syntaxToString s

