module Main where

import qualified Cobweb as W
import qualified Cobweb.Fold as W
import qualified Data.Conduit as C
import qualified Data.Conduit.List as C
import qualified Data.Machine as M
import qualified Data.Machine.Runner as M
import qualified Pipes as P
import qualified Pipes.Prelude as P
import qualified Streaming as S
import qualified Streaming.Prelude as S

import Criterion.Main (bench, bgroup, defaultMain, nf, whnf)
import Data.Functor.Identity (Identity(Identity, runIdentity))

runCobwebPure :: W.Effect Identity c -> c
runCobwebPure = runIdentity . W.run

main :: IO ()
main =
  defaultMain
    [ bgroup
        "sum"
        [ bench "cobweb" $ whnf sumW value
        , bench "conduit" $ whnf sumC value
        , bench "pipes" $ whnf sumP value
        , bench "machines" $ whnf sumM value
        , bench "streaming" $ whnf sumS value
        ]
    ]
  where
    value :: Int
    value = 1000000

sumW :: Int -> Int
{-# NOINLINE sumW #-}
sumW n = runIdentity $ W.foldNode_ (+) 0 id (W.each [1..n])

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
