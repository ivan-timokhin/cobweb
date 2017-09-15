{-|
Module: Cobweb.Unzip
Description: Unzipping value streams.
Copyright: 2017 © Ivan Timokhin
License: BSD3
Maintainer: timokhin.iv@gmail.com
Stability: experimental

This module provides functionality for splitting streams of values in
a manner reminiscent of 'Data.List.unzip' from @base@.

Note that, unlike their list counterparts, functions from this module
and "Cobweb.Zip" do /not/ cancel each other out; while functions in
"Cobweb.Zip" merge channels from /different/ 'Node's, functions in
this module split the channel into a multiple channels on the /same/
node.  That is to say, it is impossible to split a 'Node' in two
original ones after they were merged using a function from
"Cobweb.Zip", and it is likewise impossible to merge two channels
after they have been split using this module (it may technically be
possible to fuse them together via "Cobweb.Fuse", but that won't
recover original channel).

Note also that, unlike "Cobweb.Zip", this module does not provide
functor-generic functions; 'Cobweb.Core.forsOn' is strictly more
general, and allows easier specification of exact desired semantics.
-}
{-# OPTIONS_HADDOCK show-extensions #-}
{-# LANGUAGE BangPatterns #-}
{-# LANGUAGE DataKinds #-}

module Cobweb.Unzip where

import Control.Monad (forever)

import Cobweb.Core
       (Awaiting, Yielding, awaitOn, i0, i1, i2, i3, yieldOn)
import Cobweb.Internal (Node)

-- | Split a stream of values in two with provided function.
unzippingWith ::
     Functor m
  => (a -> (b, c))
  -> Node '[ Awaiting a, Yielding b, Yielding c] m r
unzippingWith f =
  forever $ do
    a <- awaitOn i0
    let !(b, c) = f a
    yieldOn i1 b
    yieldOn i2 c

-- Why the bang?  Well, we're really only using a tuple as a way to
-- get multiple values out of the function (in fact, unboxed tuple
-- would fit the bill perfectly well).  Given that the first yieldOn
-- yields control for an indefinite amount of time, it would be a
-- shame if we retained the reference to b through c's thunk for all
-- that time.  So, strictness.

-- | Split a stream of pairs into a pair of streams.
--
-- @
-- 'unzipping' = 'unzippingWith' 'id'
-- @
unzipping :: Functor m => Node '[ Awaiting (a, b), Yielding a, Yielding b] m r
unzipping = unzippingWith id

-- | Split a stream of values in three with provided function.
unzippingWith3 ::
     Functor m
  => (a -> (b, c, d))
  -> Node '[ Awaiting a, Yielding b, Yielding c, Yielding d] m r
unzippingWith3 f =
  forever $ do
    a <- awaitOn i0
    let !(b, c, d) = f a
    yieldOn i1 b
    yieldOn i2 c
    yieldOn i3 d

-- | Split a stream of triples into a triple of streams.
--
-- @
-- 'unzipping3' = 'unzippingWith3' 'id'
-- @
unzipping3 ::
     Functor m
  => Node '[ Awaiting (a, b, c), Yielding a, Yielding b, Yielding c] m r
unzipping3 = unzippingWith3 id

-- | Duplicate values of the incoming stream on both outgoing ones.
tee :: Functor m => Node '[ Awaiting a, Yielding a, Yielding a] m r
tee = unzippingWith (\x -> (x, x))
