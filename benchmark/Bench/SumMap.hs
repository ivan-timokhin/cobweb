module Bench.SumMap
  ( benchSumMap
  ) where

import qualified Cobweb as W
import qualified Data.Conduit as C
import qualified Data.Conduit.List as C
import qualified Data.Machine as M
import qualified Data.Machine.Runner as M
import qualified Pipes as P
import qualified Pipes.Prelude as P
import qualified Streaming.Prelude as S
import qualified Data.List as L

import Criterion.Main (Benchmark, bench, bgroup, whnf)
import Data.Functor.Identity (Identity(runIdentity))

benchSumMap :: Int -> Benchmark
benchSumMap n =
  bgroup
    "map+sum"
    [ bench "cobweb" $ whnf sumMapW n
    , bench "conduit" $ whnf sumMapC n
    , bench "pipes" $ whnf sumMapP n
    , bench "machines" $ whnf sumMapM n
    , bench "streaming" $ whnf sumMapS n
    , bench "list" $ whnf sumMapL n
    ]

sumMapW :: Int -> Int
{-# NOINLINE sumMapW #-}
sumMapW n =
  runIdentity $ W.foldNode_ (+) 0 id $ W.each [1 .. n] W.>-> W.mapping (+ 2)

sumMapC :: Int -> Int
{-# NOINLINE sumMapC #-}
sumMapC n =
  C.runConduitPure $ C.enumFromTo 1 n C..| C.map (+ 2) C..| C.fold (+) 0

sumMapP :: Int -> Int
{-# NOINLINE sumMapP #-}
sumMapP n = runIdentity $ P.fold (+) 0 id (P.each [1 .. n] P.>-> P.map (+ 2))

sumMapM :: Int -> Int
{-# NOINLINE sumMapM #-}
sumMapM n =
  runIdentity $ M.foldlT (+) 0 (M.enumerateFromTo 1 n M.~> M.auto (+ 2))

sumMapS :: Int -> Int
{-# NOINLINE sumMapS #-}
sumMapS n = runIdentity $ S.fold_ (+) 0 id $ S.map (+ 2) $ S.each [1 .. n]

sumMapL :: Int -> Int
{-# NOINLINE sumMapL #-}
sumMapL n = L.foldl' (+) 0 $ L.map (+ 2) [1 .. n]
