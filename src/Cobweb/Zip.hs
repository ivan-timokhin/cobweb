{-# LANGUAGE DataKinds #-}

module Cobweb.Zip where

import Control.Monad (forever)

import Cobweb.Core (Awaiting, Yielding, awaitOn, yieldOn)
import Cobweb.Internal (Node)
import Cobweb.Type.Combinators (i0, i1, i2)

zipping ::
     Functor m
  => (a -> b -> c)
  -> Node '[ Awaiting a, Awaiting b, Yielding c] m r
zipping f =
  forever $ do
    a <- awaitOn i0
    b <- awaitOn i1
    yieldOn i2 (f a b)

tee :: Functor m => Node '[ Awaiting a, Yielding a, Yielding a] m r
tee =
  forever $ do
    a <- awaitOn i0
    yieldOn i1 a
    yieldOn i2 a
