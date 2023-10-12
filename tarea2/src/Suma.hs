module Suma ( sumaCuadradosR
            , sumaCuadradosC
            ) where

sumaCuadradosR :: Integer -> Integer
sumaCuadradosR 0 = 0
sumaCuadradosR n = n^2 + sumaCuadradosR (n-1)

sumaCuadradosC :: Integer -> Integer
sumaCuadradosC n = sum [x^2 | x <- [0..n]]
