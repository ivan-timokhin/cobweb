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
      -- This benchmark in /incredibly/ fishy.  Brief inspection of
      -- Core and/or list of fired rewrite rules shows that
      -- build/foldr fusion happens in 'sumW' and 'sumL' and NOWHERE
      -- ELSE (maybe sumC, but I don't quite understand what's
      -- happening there).  This is especially mysterious in case of
      -- @machines@, where the generated list literally lives and dies
      -- within the library, and yet makes it into the Core.  This
      -- creeps me out, but I have no idea of how to fix that.
    "sum"
    [ bench "cobweb" $ whnf sumW n
    , bench "conduit" $ whnf sumC n
    , bench "pipes" $ whnf sumP n
    , bench "machines" $ whnf sumM n
    , bench "streaming" $ whnf sumS n
    , bench "list" $ whnf sumL n
    ]

sumW :: Int -> Int
{-# NOINLINE sumW #-}
sumW n = runIdentity $ W.foldNode_ (+) 0 id (W.each [1 .. n])

sumC :: Int -> Int
{-# NOINLINE sumC #-}
sumC n = C.runConduitPure $ C.enumFromTo 1 n C..| C.fold (+) 0

sumP :: Int -> Int
{-# NOINLINE sumP #-}
sumP n = runIdentity $ P.fold (+) 0 id (P.each [1 .. n])

sumM :: Int -> Int
{-# NOINLINE sumM #-}
sumM n = runIdentity $ M.foldlT (+) 0 (M.enumerateFromTo 1 n)

sumS :: Int -> Int
{-# NOINLINE sumS #-}
sumS n = runIdentity $ S.fold_ (+) 0 id (S.each [1 .. n])

sumL :: Int -> Int
{-# NOINLINE sumL #-}
sumL n = L.foldl' (+) 0 [1 .. n]
