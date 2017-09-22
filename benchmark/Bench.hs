module Main where

import Criterion.Main (defaultMain)

import Bench.Sum (benchSum)
import Bench.SumMap (benchSumMap)

main :: IO ()
main = defaultMain [benchSum value, benchSumMap value]
  where
    value :: Int
    value = 1000000
