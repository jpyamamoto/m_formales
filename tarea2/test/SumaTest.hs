module SumaTest (main) where

import Test.Hspec
import Test.QuickCheck

import Suma
import Data.Ratio

prop_suma :: (NonNegative Integer) -> Bool
prop_suma (NonNegative n) = toRational (sumaCuadradosR n) == (n * (n + 1) * (2 * n + 1)) % 6


prop_suma_equiv :: (NonNegative Integer) -> Bool
prop_suma_equiv (NonNegative n) = sumaCuadradosR n == sumaCuadradosC n

main :: IO ()
main = hspec $ do
  describe "Sum of squared naturals is given by formula" $
    do it "prop_suma" $ property prop_suma

  describe "Functions for summing squares are equivalent" $
    do it "prop_suma_equiv" $ property prop_suma_equiv
