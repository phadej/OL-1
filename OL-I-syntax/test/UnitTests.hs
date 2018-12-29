module Main (main) where

import Test.QuickCheck       (Property, counterexample, (===))
import Test.Tasty            (defaultMain, testGroup)
import Test.Tasty.QuickCheck (testProperty)

import OL1.Syntax

main :: IO ()
main = defaultMain $ testGroup "Properties"
    [ testProperty "roundtrip" roundtripProp
    ]

roundtripProp :: Syntax I -> Property
roundtripProp s = counterexample str $ case syntaxFromString str of
    Right (s' :~ _) -> counterexample (show s') $ s === hoistSyntax spannedToI s'
    Left err        -> counterexample err False
  where
    str = syntaxToString s

