{-# LANGUAGE DataKinds #-}

module Cobweb.Producer where

import Cobweb.Core (Yielding, eachOn, forOn)
import Cobweb.Internal (Node)
import Cobweb.Type.Combinators (All, i0)

type Producer a = Node '[ Yielding a]

each :: (Foldable f, Functor m) => f a -> Producer a m ()
each = eachOn i0

for ::
     (All Functor cs, Functor m)
  => Producer a m r
  -> (a -> Node cs m ())
  -> Node cs m r
for = forOn i0
