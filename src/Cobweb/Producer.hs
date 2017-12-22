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
{-# OPTIONS_GHC -Wno-missing-import-lists #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE TypeFamilies #-}

module Cobweb.Producer
  ( Producer
  , Yield
  , yield
  , each
  , generate
  , mapP
  , for
  , next
  , produceOn
  , span
  , splitAt
  ) where

import Prelude hiding (span, splitAt)

import Control.Monad (forever)
import Control.Monad.Trans (lift)
import Type.Family.List (Last, Null)
import Data.Functor.Coyoneda (lowerCoyoneda)

import Cobweb.Core
  ( Leaf
  , Producer
  , Yield
  , connect
  , eachOn
  , forOn
  , inspectLeaf
  , leafOn
  , mapOn
  , yieldOn
  )
import Cobweb.Internal (Node, build, unconsNode)
import Cobweb.Type.Combinators (IIndex, Inductive, fsumOnly, i0, lastIndex)

-- | Produce a value on the last channel of a 'Node'.
--
-- This function can be thought of as having any of the following types:
--
-- @
-- 'yield' :: b -> 'Producer' b m ()
-- 'yield' :: b -> 'Cobweb.Pipe.Pipe' a b m ()
-- @
--
-- ====__What are all these constraints?__
--
--    [@'Known' 'Length' cs@] This is mostly an implementation detail;
--        while it means what it says, all actual lists have known
--        length, so this shouldn't be an issue.
--
--    [@'Last' cs ~ 'Yield' a@] The last channel in the list (the
--        one we'll be using) is @'Yield' a@, i.e. produces values
--        of type @a@.
--
--    [@'Null' cs ~ ''False'@] The channel list should not be empty.
yield ::
     (Inductive cs, Last cs ~ Yield a, Null cs ~ 'False)
  => a
  -> Node cs m ()
yield = yieldOn lastIndex

-- | Yield each value in order.
each :: Foldable f => f a -> Producer a m ()
{-# INLINE each #-}
each = eachOn i0

-- | Generate an infinite stream of values by repeatedly running the
-- provided action.
generate :: Monad m => m a -> Producer a m r
generate source =
  forever $ do
    a <- lift source
    yield a

-- | Apply a function to all yielded values.
mapP :: (a -> b) -> Producer a m () -> Producer b m ()
mapP = mapOn i0

-- | Loop over a producer.
for ::
     Inductive cs
  => Producer a m r -- ^ Source of values.
  -> (a -> Node cs m ()) -- ^ Loop body.
  -> Node cs m r
for = forOn i0

-- | Run a 'Producer' until it either terminates, or produces a
-- value.  In the latter case, returns the value along with the rest
-- of the 'Producer'
next :: Monad m => Producer a m r -> m (Either r (a, Producer a m r))
next = fmap (fmap lowerCoyoneda) . inspectLeaf

-- | Embed a 'Producer' into a larger 'Node', by identifying its sole
-- output channel with a matching channel in the outer 'Node'.
--
-- ====__Signatures for some specific indices__
-- @
-- 'produceOn' 'i0' ::
--       'Functor' m
--    => 'Producer' a m r
--    -> 'Node' ('Yield' a : cs) m r
--
-- 'produceOn' 'Cobweb.Core.i1' ::
--       'Functor' m
--    => 'Producer' a m r
--    -> 'Node' (c0 : 'Yield' a : cs) m r
--
-- 'produceOn' 'Cobweb.Core.i2' ::
--       'Functor' m
--    => 'Producer' a m r
--    -> 'Node' (c0 : c1 : 'Yield' a : cs) m r
-- @
produceOn ::
     Inductive cs
  => IIndex n cs (Yield a) -- ^ A channel to attach to.
  -> Producer a m r
  -> Node cs m r
produceOn = leafOn

-- | Produce all elements up to the first one that violates the
-- predicate (non-inclusive), then return the rest of the stream.
--
-- A moral equivalent of 'Data.List.span'.
span :: (a -> Bool) -> Producer a m r -> Producer a m (Producer a m r)
span predicate node =
  build
    (\ret con lft ->
       let loop =
             unconsNode
               (ret . pure)
               (\cs cont ->
                  let (a, _) = fsumOnly cs
                  in if predicate a
                       then con cs (loop . cont)
                       else ret (connect cs >>= cont))
               (\eff cont -> lft eff (loop . cont))
       in loop node)

-- | Split the stream at @n@th connection, and return the rest.
--
-- While this function is technically functor-generic, semantics are
-- tied to 'Producer'-like 'Node's.  In particular, the ‘outer’ 'Leaf'
-- terminates immediately after the @n@th connection, which makes
-- perfect sense for 'Producer's, which typically have
-- connection-associated actions /before/ the actual connection, but
-- not for consumers.
--
-- A moral equivalent of 'Data.List.splitAt'; see also
-- 'Cobweb.Consumer.splitAt'.
splitAt :: Int -> Leaf c m a -> Leaf c m (Leaf c m a)
splitAt n node =
  build
    (\ret con lft ->
       let loop k
             | k <= 0 = ret
           loop k =
             unconsNode
               (ret . pure)
               (\c cont -> con c (loop (k - 1) . cont))
               (\eff cont -> lft eff (loop k . cont))
       in loop n node)
