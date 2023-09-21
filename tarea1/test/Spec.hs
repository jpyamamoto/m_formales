module Main (main) where

import Test.QuickCheck
import qualified MsortTest as Msort
import qualified IsortTest as Isort

main = do
  Msort.main
  Isort.main
