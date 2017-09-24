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
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE TypeOperators #-}

module Cobweb.Consumer
  ( Consumer
  , Awaiting
  , await
  , drain
  , discard
  , premap
  , prefor
  , nextRequest
  , consumeOn
  , splitAt
  ) where

import Prelude hiding (splitAt)

import Control.Monad (forever)
import Control.Monad.Trans (lift)

import Cobweb.Core
       (Awaiting, Consumer, Leaf, Node, awaitOn, i0, inspectLeaf, leafOn,
        preforOn, premapOn)
import Cobweb.Internal (Node(Connect, Effect, Return))
import Cobweb.Type.Combinators (All, IIndex)

-- | Produce a value on the first channel of a 'Node'.
--
-- This function can be thought of as having any of the following
-- types:
--
-- @
-- 'await' :: 'Consumer' a m a
-- 'await' :: 'Cobweb.Pipe.Pipe' a b m a
-- @
await :: Node (Awaiting a : cs) m a
await = awaitOn i0

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
premap :: Functor m => (b -> a) -> Consumer a m r -> Consumer b m r
premap = premapOn i0

-- | Loop over a consumer.
--
-- Each time the consumer 'await's, second argument is run to
-- determine the value that the consumer will receive.
prefor ::
     (All Functor cs, Functor m)
  => Consumer a m r -- ^ Consumer of values.
  -> Node cs m a -- ^ Provider of values.
  -> Node cs m r
prefor = preforOn i0

-- | Run a 'Consumer' until it either terminates, or requests a value
-- to continue.
--
-- @
-- 'nextRequest' = 'inspectLeaf'
-- @
nextRequest :: Monad m => Consumer a m r -> m (Either r (a -> Consumer a m r))
nextRequest = inspectLeaf

-- | Embed a 'Consumer' into a larger 'Node', by identifying its sole
-- input channel with a matching one in a larger list.
--
-- ====__Signatures for some specific indices__
-- @
-- 'consumeOn' 'i0' ::
--       'Functor' m
--    => 'Consumer' a m r
--    -> 'Node' ('Awaiting' a : cs) m r
--
-- 'consumeOn' 'Cobweb.Core.i1' ::
--       'Functor' m
--    => 'Consumer' a m r
--    -> 'Node' (c0 : 'Awaiting' a : cs) m r
--
-- 'consumeOn' 'Cobweb.Core.i2' ::
--       'Functor' m
--    => 'Consumer' a m r
--    -> 'Node' (c0 : c1 : 'Awaiting' a : cs) m r
-- @
consumeOn ::
     Functor m => IIndex n cs (Awaiting a) -> Consumer a m r -> Node cs m r
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
splitAt :: (Functor c, Functor m) => Int -> Leaf c m r -> Leaf c m (Leaf c m r)
splitAt _ (Return r) = Return (pure r)
splitAt n (Effect eff) = Effect (fmap (splitAt n) eff)
splitAt n node@(Connect con)
  | n <= 0 = pure node
  | otherwise = Connect (fmap (splitAt (n - 1)) con)
