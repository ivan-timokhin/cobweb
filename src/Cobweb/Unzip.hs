{-# LANGUAGE DataKinds #-}

module Cobweb.Unzip where

import Control.Monad (forever)

import Cobweb.Core (Awaiting, Yielding, awaitOn, yieldOn)
import Cobweb.Internal (Node)
import Cobweb.Type.Combinators (i0, i1, i2)

unzipping ::
     Functor m
  => (a -> (b, c))
  -> Node '[ Awaiting a, Yielding b, Yielding c] m r
unzipping f =
  forever $ do
    a <- awaitOn i0
    let (b, c) = f a
    yieldOn i1 b
    yieldOn i2 c

tee :: Functor m => Node '[ Awaiting a, Yielding a, Yielding a] m r
tee =
  forever $ do
    a <- awaitOn i0
    yieldOn i1 a
    yieldOn i2 a
