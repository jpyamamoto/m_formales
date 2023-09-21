module MsortTest (main) where

import Test.Hspec
import Test.QuickCheck

import Data.List
import Msort

isSorted :: Ord a => [a] -> Bool
isSorted []  = True
isSorted [a] = True
isSorted (x:y:xs) = x <= y && isSorted (y:xs)

prop_msort_ordered :: [Int] -> Bool
prop_msort_ordered xs = isSorted $ msort xs

prop_msort_sameElems :: [Int] -> Bool
prop_msort_sameElems l = length l == length sorted
                         && isSubset l sorted
                         && isSubset sorted l
  where sorted = msort l
        isSubset xs ys = null $ xs \\ ys

prop_msort_first :: [Int] -> Property
prop_msort_first xs = not (null xs) ==> (head sorted == minimum sorted)
  where sorted = msort xs

main :: IO ()
main = hspec $ do
  describe "List is sorted after msort" $
    do it "prop_msort_ordered" $ property prop_msort_ordered
  describe "List has the same elements after sorted" $
    do it "prop_msort_sameElems" $ property prop_msort_sameElems
  describe "First element of sorted list is the minimum" $
    do it "prop_msort_first" $ property prop_msort_first
