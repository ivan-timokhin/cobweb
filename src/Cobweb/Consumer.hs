{-|
Module: Cobweb.Consumer
Description: Nodes that only await values.
Copyright: 2017 © Ivan Timokhin
License: BSD3
Maintainer: timokhin.iv@gmail.com
Stability: experimental

Nodes that only await values.

Some of the functions in this module have channel- and functor-generic
counterparts in "Cobweb.Core"; these are specialised for 'Consumer's.
-}
{-# OPTIONS_HADDOCK show-extensions #-}
{-# OPTIONS_GHC -Wno-missing-import-lists #-}
{-# LANGUAGE BangPatterns #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE TypeOperators #-}

module Cobweb.Consumer
  ( Consumer
  , Await
  , await
  , drain
  , discard
  , contramap
  , contrafor
  , nextRequest
  , consumeOn
  , splitAt
  ) where

import Prelude hiding (splitAt)

import Control.Monad (forever)
import Control.Monad.Trans (lift)
import Data.Functor.Coyoneda (lowerCoyoneda)

import Cobweb.Core
  ( Await
  , Consumer
  , Leaf
  , Node
  , awaitOn
  , connect
  , contraforOn
  , contramapOn
  , i0
  , inspectLeaf
  , leafOn
  )
import Cobweb.Internal (build, unconsNode)
import Cobweb.Type.Combinators (IIndex, Inductive)

-- | Produce a value on the first channel of a 'Node'.
--
-- This function can be thought of as having any of the following
-- types:
--
-- @
-- 'await' :: 'Consumer' a m a
-- 'await' :: 'Cobweb.Pipe.Pipe' a b m a
-- @
await :: Inductive cs => Node (Await a : cs) m a
{-# NOINLINE await #-}
await = awaitOn i0

-- GHC refuses to inline @await@ normally (probably because it's just
-- a value, and it can't see any benefit in inlining it), so here's a
-- more forceful version.
{-# RULES "cobweb/await" await = awaitOn i0 #-}

-- | Consume values indefinitely, by feeding them into a provided
-- action.
drain :: Monad m => (a -> m ()) -> Consumer a m r
drain sink = forever $ do
  a <- await
  lift $ sink a

-- | Simply discards the argument.
--
-- @
-- 'discard' = 'const' ('pure' ())
-- @
--
-- This is intended for use with 'drain': @'drain' 'discard'@ is a
-- 'Consumer' that receives values indefinitely, and does nothing with
-- them.
discard :: Applicative f => a -> f ()
discard = const (pure ())

-- | Apply a function to all incoming values.
contramap :: (b -> a) -> Consumer a m r -> Consumer b m r
contramap = contramapOn i0

-- | Loop over a consumer.
--
-- Each time the consumer 'await's, second argument is run to
-- determine the value that the consumer will receive.
contrafor ::
     Inductive cs
  => Consumer a m r -- ^ Consumer of values.
  -> Node cs m a -- ^ Provider of values.
  -> Node cs m r
contrafor = contraforOn i0

-- | Run a 'Consumer' until it either terminates, or requests a value
-- to continue.
--
-- @
-- 'nextRequest' = 'inspectLeaf'
-- @
nextRequest :: Monad m => Consumer a m r -> m (Either r (a -> Consumer a m r))
nextRequest = fmap (fmap lowerCoyoneda) . inspectLeaf

-- | Embed a 'Consumer' into a larger 'Node', by identifying its sole
-- input channel with a matching one in a larger list.
--
-- ====__Signatures for some specific indices__
-- @
-- 'consumeOn' 'i0' ::
--       'Functor' m
--    => 'Consumer' a m r
--    -> 'Node' ('Await' a : cs) m r
--
-- 'consumeOn' 'Cobweb.Core.i1' ::
--       'Functor' m
--    => 'Consumer' a m r
--    -> 'Node' (c0 : 'Await' a : cs) m r
--
-- 'consumeOn' 'Cobweb.Core.i2' ::
--       'Functor' m
--    => 'Consumer' a m r
--    -> 'Node' (c0 : c1 : 'Await' a : cs) m r
-- @
consumeOn ::
     Inductive cs => IIndex n cs (Await a) -> Consumer a m r -> Node cs m r
consumeOn = leafOn

-- | Split the stream before @(n + 1)@th connection, and return the
-- rest.
--
-- While this function is technically functor-generic, semantics are
-- tied to 'Consumer'-like 'Node's.  In particular, the ‘outer’
-- terminates immediately before the @(n + 1)@th connection, which
-- makes perfect sense for 'Consumer's, which typically have
-- connection-associated actions /after/ the actual connection, but
-- not so for producers.
--
-- See also 'Cobweb.Producer.splitAt'
splitAt :: Int -> Leaf c m r -> Leaf c m (Leaf c m r)
splitAt n node =
  build
    (\ret con lft ->
       let loop !k =
             unconsNode
               (ret . pure)
               (\c cont ->
                  if k <= 0
                    then ret (connect c >>= cont)
                    else con c (loop (k - 1) . cont))
               (\eff cont -> lft eff (loop k . cont))
       in loop n node)
