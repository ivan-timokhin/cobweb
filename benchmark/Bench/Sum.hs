module Bench.Sum
  ( benchSum
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

benchSum :: Int -> Benchmark
benchSum n =
  bgroup
    "sum"
    [ bgroup
        "fusion"
        [ bench "cobweb" $ whnf sumW n
        , bench "conduit" $ whnf sumC n
        , bench "pipes" $ whnf sumP n
        , bench "machines" $ whnf sumM n
        , bench "streaming" $ whnf sumS n
        , bench "list" $ whnf sumL n
        ]
    , bgroup
        "no fusion"
        [ bench "cobweb" $ whnf sumW' n
        , bench "conduit" $ whnf sumC' n
        , bench "pipes" $ whnf sumP' n
        , bench "machines" $ whnf sumM' n
        , bench "streaming" $ whnf sumS' n
        , bench "list" $ whnf sumL' n
        ]
    ]

sumW :: Int -> Int
{-# NOINLINE sumW #-}
sumW n = runIdentity $ W.foldNode_ (+) 0 id (W.each [1 .. n])

producerW :: Int -> W.Producer Int Identity ()
{-# NOINLINE producerW #-}
producerW n = W.each [1..n]

sumW' :: Int -> Int
{-# NOINLINE sumW' #-}
sumW' n = runIdentity $ W.foldNode_ (+) 0 id (producerW n)

sumC :: Int -> Int
{-# NOINLINE sumC #-}
sumC n = C.runConduitPure $ C.enumFromTo 1 n C..| C.fold (+) 0

producerC :: Int -> C.ConduitM i Int Identity ()
{-# NOINLINE producerC #-}
producerC = C.enumFromTo 1

sumC' :: Int -> Int
{-# NOINLINE sumC' #-}
sumC' n = C.runConduitPure $ producerC n C..| C.fold (+) 0

sumP :: Int -> Int
{-# NOINLINE sumP #-}
sumP n = runIdentity $ P.fold (+) 0 id (P.each [1 .. n])

producerP :: Int -> P.Producer Int Identity ()
{-# NOINLINE producerP #-}
producerP n = P.each [1 .. n]

sumP' :: Int -> Int
{-# NOINLINE sumP' #-}
sumP' n = runIdentity $ P.fold (+) 0 id (producerP n)

sumM :: Int -> Int
{-# NOINLINE sumM #-}
sumM n = runIdentity $ M.foldlT (+) 0 (M.enumerateFromTo 1 n)

producerM :: Int -> M.MachineT Identity k Int
{-# NOINLINE producerM #-}
producerM = M.enumerateFromTo 1

sumM' :: Int -> Int
{-# NOINLINE sumM' #-}
sumM' n = runIdentity $ M.foldlT (+) 0 (producerM n)

sumS :: Int -> Int
{-# NOINLINE sumS #-}
sumS n = runIdentity $ S.fold_ (+) 0 id (S.each [1 .. n])

producerS :: Int -> S.Stream (S.Of Int) Identity ()
{-# NOINLINE producerS #-}
producerS n = S.each [1 .. n]

sumS' :: Int -> Int
{-# NOINLINE sumS' #-}
sumS' n = runIdentity $ S.fold_ (+) 0 id (producerS n)

sumL :: Int -> Int
{-# NOINLINE sumL #-}
sumL n = L.foldl' (+) 0 [1 .. n]

producerL :: Int -> [Int]
{-# NOINLINE producerL #-}
producerL n = [1 .. n]

sumL' :: Int -> Int
{-# NOINLINE sumL' #-}
sumL' n = L.foldl' (+) 0 (producerL n)
