{-|
Module: Cobweb.Zip
Description: Zipping multiple Nodes together.
Copyright: 2017 © Ivan Timokhin
License: BSD3
Maintainer: timokhin.iv@gmail.com
Stability: experimental

This module provides functionality for merging streams of values
together in a manner reminiscent of 'Data.List.zip' from @base@.

Note that, even though it is possible to have multiple streams of
values on one 'Node', it is not possible to merge them in this
fashion; zipping is only supported for channels on /different/
'Node's.

-}
{-# OPTIONS_HADDOCK show-extensions #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeOperators #-}

module Cobweb.Zip
  (
    -- * Specialised
    -- $specialised
    zippingWith
  , zipping
  , zippingWith3
  , zipping3
    -- * Generic
    -- $generic
  , zipsWith
  , zips
  ) where

import Control.Applicative (liftA2)
import Control.Monad (forever)
import Data.Proxy (Proxy(Proxy))
import Data.Type.Length (Length)
import Data.Type.Sum.Lifted (FSum(FInL, FInR))
import Type.Class.Known (Known)
import Type.Family.List (type (++))

import Cobweb.Core (Awaiting, Yielding, awaitOn, yieldOn)
import Cobweb.Internal
       (Node(Node, getNode), NodeF(ConnectF, EffectF, ReturnF))
import Cobweb.Type.Combinators
       (All, IIndex, IWithout, fdecompIdx, finl, finr, i0, i1, i2, i3)

-- $specialised
--
-- This section contains functions dedicated specifically to merging
-- 'Yielding' streams.  Concretely, they are provided in a form of
-- 'Node's that can be linked with actual producers using functions
-- from "Cobweb.Link" module.

-- | Merge two incoming streams of values in a pairwise manner using a
-- supplied function.
--
-- The values on the first channel are requested first.
--
-- ====__Example__
--
-- @
-- 'Cobweb.Core.run' '$' 'Cobweb.Producer.each' [\'H\', \'W\', \'Z\'] 'Cobweb.Link.>-|'
--     'Cobweb.Producer.each' ["ello", "orld!"] 'Cobweb.Link.>-|' 'zippingWith' (:) 'Cobweb.Link.>->' 'Cobweb.Consumer.drain' 'print'
-- @
--
-- prints
--
-- > "Hello"
-- > "World!"
zippingWith ::
     Functor m
  => (a -> b -> c)
  -> Node '[ Awaiting a, Awaiting b, Yielding c] m r
zippingWith f =
  forever $ do
    a <- awaitOn i0
    b <- awaitOn i1
    yieldOn i2 (f a b)

-- | Merges two incoming streams of values pairwise.
--
-- @
-- 'zipping' = 'zippingWith' (,)
-- @
zipping :: Functor m => Node '[ Awaiting a, Awaiting b, Yielding (a, b)] m r
zipping = zippingWith (,)

-- | Merges three streams of values, same as 'zippingWith'.
--
-- Values are requested in the order of the channels.
zippingWith3 ::
     Functor m
  => (a -> b -> c -> d)
  -> Node '[ Awaiting a, Awaiting b, Awaiting c, Yielding d] m r
zippingWith3 f =
  forever $ do
    a <- awaitOn i0
    b <- awaitOn i1
    c <- awaitOn i2
    yieldOn i3 (f a b c)

-- | Merges three streams of values, same as 'zipping'.
--
-- @
-- 'zipping3' = 'zippingWith3' (,,)
-- @
zipping3 ::
     Functor m
  => Node '[ Awaiting a, Awaiting b, Awaiting c, Yielding (a, b, c)] m r
zipping3 = zippingWith3 (,,)

-- $generic
--
-- This section contains functions for merging channels using
-- arbitrary connection functors.  Since linking such channels fully
-- generically is impossible, the functions provided here instead take
-- 'Node's containing channels to be zipped as arguments, and returns
-- a ‘merged’ 'Node'.
--
-- As a general note, 'Node's are run in the order of the arguments;
-- that is, first syntactically first 'Node' is run until either
-- termination or connection on the specified channel, then same with
-- second 'Node', then merge the connections, and repeat anew.

-- | Zip two channels together via a supplied function.
zipsWith ::
     forall n k lcs rcs lcs' rcs' lc rc c m r.
     ( IWithout n lcs lcs'
     , IWithout k rcs rcs'
     , Known Length lcs'
     , All Functor lcs'
     , All Functor rcs'
     , Functor c
     , Functor m
     )
  => (forall x y. lc x -> rc y -> c (x, y)) -- ^ Combine connections
     -- on two channels in one.
  -> IIndex n lcs lc -- ^ Index of the zipped channel on the first 'Node'.
  -> IIndex k rcs rc -- ^ Index of the zipped channel on the second 'Node'.
  -> Node lcs m r
  -> Node rcs m r
  -> Node (c : (lcs' ++ rcs')) m r
zipsWith combine n k = flip loopLeft
  where
    loopLeft :: Node rcs m r -> Node lcs m r -> Node (c : (lcs' ++ rcs')) m r
    loopLeft right left =
      Node $
      case getNode left of
        ReturnF r -> ReturnF r
        EffectF eff -> EffectF (fmap (loopLeft right) eff)
        ConnectF con ->
          case fdecompIdx n con of
            Left other ->
              ConnectF (FInR $ finl proxyR (fmap (loopLeft right) other))
            Right c -> getNode $ loopRight c right
    loopRight ::
         lc (Node lcs m r) -> Node rcs m r -> Node (c : (lcs' ++ rcs')) m r
    loopRight left right =
      Node $
      case getNode right of
        ReturnF r -> ReturnF r
        EffectF eff -> EffectF (fmap (loopRight left) eff)
        ConnectF con ->
          case fdecompIdx k con of
            Left other ->
              ConnectF (FInR $ finr proxyL (fmap (loopRight left) other))
            Right c ->
              ConnectF (FInL $ fmap (uncurry (flip loopLeft)) (combine left c))
    proxyL :: Proxy lcs'
    proxyL = Proxy
    proxyR :: Proxy rcs'
    proxyR = Proxy

-- | Same as 'zipsWith', but use 'Applicative' instance of the common
-- channel to merge connections.
--
-- For common channel types, this means
--
--  [@'Yielding' a@] adds a 'Monoid' constraint on @a@, and combines
--                   yielded values via 'mappend'.
--
--  [@'Awaiting' a@] receive one value, then use it to satisfy both
--                   requests.
--
-- @
-- 'zips' = 'zipsWith' ('liftA2' (,))
-- @
zips ::
     ( IWithout n lcs lcs'
     , IWithout k rcs rcs'
     , Known Length lcs'
     , All Functor lcs'
     , All Functor rcs'
     , Applicative c
     , Functor m
     )
  => IIndex n lcs c -- ^ Index of the zipped channel on the first 'Node'.
  -> IIndex k rcs c -- ^ Index of the zipped channel on the second 'Node'.
  -> Node lcs m r
  -> Node rcs m r
  -> Node (c : (lcs' ++ rcs')) m r
zips = zipsWith (liftA2 (,))
