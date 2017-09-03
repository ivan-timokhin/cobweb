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
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE TypeFamilies #-}

module Cobweb.Producer
  ( Producer
  , Yielding
  , yield
  , each
  , mapP
  , for
  , next
  , produceOn
  ) where

import Data.Type.Length (Length)
import Type.Class.Known (Known)
import Type.Family.List (Last, Null)

import Cobweb.Core
       (Producer, Yielding, eachOn, forOn, inspectLeaf, mapOn, mapsAll,
        yieldOn)
import Cobweb.Internal (Node)
import Cobweb.Type.Combinators
       (All, IIndex, finjectIdx, fsumOnly, i0, lastIndex)

-- | Produce a value on the last channel of a 'Node'.
--
-- This function can be thought of as having any of the following types:
--
-- @
-- 'yield' :: 'Functor' m => b -> 'Producer' b m ()
-- 'yield' :: 'Functor' m => b -> 'Cobweb.Pipe.Pipe' a b m ()
-- @
--
-- ====__What are all these constraints?__
--
--    [@'Known' 'Length' cs@] This is mostly an implementation detail;
--        while it means what it says, all actual lists have known
--        length, so this shouldn't be an issue.
--
--    [@'Last' cs ~ 'Yielding' a@] The last channel in the list (the
--        one we'll be using) is @'Yielding' a@, i.e. produces values
--        of type @a@.
--
--    [@'Null' cs ~ ''False'@] The channel list should not be empty.
yield ::
     (Known Length cs, Last cs ~ Yielding a, Null cs ~ 'False)
  => a
  -> Node cs m ()
yield = yieldOn lastIndex

-- | Yield each value in order.
each :: (Foldable f, Functor m) => f a -> Producer a m ()
each = eachOn i0

-- | Apply a function to all yielded values.
mapP :: Functor m => (a -> b) -> Producer a m () -> Producer b m ()
mapP = mapOn i0

-- | Loop over a producer.
for ::
     (All Functor cs, Functor m)
  => Producer a m r -- ^ Source of values.
  -> (a -> Node cs m ()) -- ^ Loop body.
  -> Node cs m r
for = forOn i0

-- | Run a 'Producer' until it either terminates, or produces a
-- value.  In the latter case, returns the value along with the rest
-- of the 'Producer'
--
-- @
-- 'next' = 'inspectLeaf'
-- @
next :: Monad m => Producer a m r -> m (Either r (a, Producer a m r))
next = inspectLeaf

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
