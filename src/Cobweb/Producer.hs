{-|
Module: Cobweb.Producer
Description: Nodes that only yield values.
Copyright: 2017 © Ivan Timokhin
License: BSD3
Maintainer: timokhin.iv@gmail.com
Stability: experimental

Nodes that only yield values.

Some of the functions in this module have channel- and functor-generic
counterparts in "Cobweb.Core"; these are specialised for 'Producer's.
-}
{-# OPTIONS_HADDOCK show-extensions #-}
{-# LANGUAGE DataKinds #-}

module Cobweb.Producer
  ( Producer
  , each
  , for
  , produceOn
  ) where

import Cobweb.Core (mapsAll, Leaf, Yielding, eachOn, forOn)
import Cobweb.Internal (Node)
import Cobweb.Type.Combinators
       (All, IIndex, finjectIdx, fsumOnly, i0)

-- | A 'Node' that only yields values on its sole open channel.
type Producer a = Leaf (Yielding a)

-- | Yield each value in the foldable container.
each :: (Foldable f, Functor m) => f a -> Producer a m ()
each = eachOn i0

-- | Loop over a producer.
for ::
     (All Functor cs, Functor m)
  => Producer a m r -- ^ Source of values.
  -> (a -> Node cs m ()) -- ^ Loop body.
  -> Node cs m r
for = forOn i0

-- | Embed a 'Producer' into a larger 'Node', by identifying its sole
-- output channel with a matching channel in the outer 'Node'.
--
-- ====__Signatures for some specific indices__
-- @
-- 'produceOn' 'i0' ::
--       'Functor' m
--    => 'Producer' a m r
--    -> 'Node' ('Yielding' a : cs) m r
--
-- 'produceOn' 'Cobweb.Core.i1' ::
--       'Functor' m
--    => 'Producer' a m r
--    -> 'Node' (c0 : 'Yielding' a : cs) m r
--
-- 'produceOn' 'Cobweb.Core.i2' ::
--       'Functor' m
--    => 'Producer' a m r
--    -> 'Node' (c0 : c1 : 'Yielding' a : cs) m r
-- @
produceOn ::
     Functor m
  => IIndex n cs (Yielding a) -- ^ A channel to attach to.
  -> Producer a m r
  -> Node cs m r
produceOn n = mapsAll (finjectIdx n . fsumOnly)
