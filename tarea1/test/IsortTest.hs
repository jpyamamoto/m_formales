module IsortTest (main) where

import Test.Hspec
import Test.QuickCheck

import Data.List
import Isort

isOrdered :: Ord a => [a] -> Bool
isOrdered []  = True
isOrdered [a] = True
isOrdered (x:y:xs) = x <= y && isOrdered (y:xs)

prop_isort_sort :: [Int] -> Bool
prop_isort_sort xs = isort xs == sort xs

-- Comentamos esta prueba, pues se agotan los ejemplares
-- generados y ocasiona una falla.
-- prop_insert_ordered :: Int -> [Int] -> Property
-- prop_insert_ordered x xs = isOrdered xs ==> isOrdered (insert x xs)

prop_insert_ordered :: Int -> (OrderedList Int) -> Bool
prop_insert_ordered x (Ordered xs) = isOrdered (insert x xs)

main :: IO ()
main = hspec $ do
  describe "List is sorted after isort" $
    do it "prop_isort_sort" $ property prop_isort_sort

  -- describe "insert preserves order (solution 1)" $
  --   do it "prop_insert_ordered" $ property prop_insert_ordered

  describe "insert preserves order" $
    do it "prop_insert_ordered" $ property prop_insert_ordered
