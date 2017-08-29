{-# LANGUAGE DataKinds #-}

module Cobweb.Pipe where

import Control.Monad (forever, replicateM_)

import Cobweb.Core (Awaiting, Yielding, awaitOn, yieldOn)
import Cobweb.Internal (Node)
import Cobweb.Type.Combinators (i0, i1)

type Pipe a b = Node '[ Awaiting a, Yielding b]

takeW :: Functor m => Int -> Node '[ Awaiting a, Yielding a] m ()
takeW n = replicateM_ n $ awaitOn i0 >>= yieldOn i1

mapping :: Functor m => (a -> b) -> Node '[ Awaiting a, Yielding b] m r
mapping f =
  forever $ do
    a <- awaitOn i0
    yieldOn i1 (f a)
