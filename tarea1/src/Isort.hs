module Isort (isort) where

import Data.List

isort :: Ord a => [a] -> [a]
isort = foldr insert []
