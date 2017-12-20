{-|
Module: Cobweb.Core
Description: Core types and functions
Copyright: 2017 © Ivan Timokhin
License: BSD3
Maintainer: timokhin.iv@gmail.com
Stability: experimental

This module provides the core functionality of the library: core type
('Node') and basic functions for manipulating it.
-}
{-# OPTIONS_HADDOCK show-extensions #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TupleSections #-}
{-# LANGUAGE TypeOperators #-}

module Cobweb.Core
  (
    -- * Types
    Node
  , Effect
  , Tube
  , Leaf
  , Yielding
  , Awaiting
  , Pipe
  , Producer
  , Consumer
    -- * Running 'Node'
  , run
  , inspect
  , inspectLeaf
    -- * Constructing 'Node'
  , unfold
    -- * Common channel indices
    -- $indices
  , i0
  , i1
  , i2
  , i3
  , i4
  , i5
  , i6
  , i7
  , i8
  , i9
  , i10
    -- * Initiating connections
  , connect
  , connectOn
  , yieldOn
  , eachOn
  , awaitOn
  , leafOn
    -- * Maps
  , gmapAll
  , gmapOn
  , gmapOnM
  , gmapOnM'
  , mapOn
  , mapOnM
  , contramapOn
  , contramapOnM
    -- * Looping over 'Node's
  , gforAll
  , gforOn
  , gforOnLeaf
  , forOn
  , forOnLeaf
  , contraforOn
  , contraforOnLeaf
  ) where

import Control.Monad (join)
import Data.Bifunctor (second, first)
import Data.Foldable (traverse_)
import Data.Proxy (Proxy(Proxy))
import Type.Class.Witness (Witness((\\)))

import Cobweb.Internal
       (Node(Connect, Effect, Return), cata, inspect, transformCons,
        unfold)
import Cobweb.Type.Combinators
       (Inductive, All, Append, FSum, IIndex, Remove, Replace, absurdFSum,
        fdecompIdx, fdecompReplaceIdx, finjectIdx, finl, finr, freplaceIdx,
        fsumOnly, i0, i1, i10, i2, i3, i4, i5, i6, i7, i8, i9, replaceIdx)
import Cobweb.Type.Lemmata
       (appendAll, ireplacedRetainsAll, iwithoutRetainsAll)

-- | A node with no channels, isomorphic to an effect in the base monad.
--
-- __See also__: 'run'
type Effect = Node '[]

-- | A node with two channels (typically, one for input and one for
-- output).
type Tube i o = Node '[i, o]

-- | A node with only one channel.
type Leaf c = Node '[ c]

-- | A channel type of @'Yielding' a@ implies that a 'Node' is
-- producing values of type @a@ on this channel.
--
-- __See also__: 'yieldOn', 'Producer'
type Yielding = (,)

-- | A channel type of @'Awaiting' a@ implies that a 'Node' is
-- receiving values of type @a@ on this channel.
--
-- __See also__: 'awaitOn', 'Consumer'
type Awaiting = (->)

-- | A 'Node' that receives values on its first channel, and produces
-- values on the second one.
type Pipe a b = Tube (Awaiting a) (Yielding b)

-- | A 'Node' that only yields values on its sole open channel.
type Producer a = Leaf (Yielding a)

-- | A 'Node' that only receives values on its sole open channel.
type Consumer a = Leaf (Awaiting a)

-- | Run a node with no open channels in the base monad.
run :: Monad m => Effect m r -> m r
{-# INLINE run #-}
run = cata pure absurdFSum join

-- | 'inspect' a 'Leaf'.
inspectLeaf ::
     (Monad m, Functor c) => Leaf c m r -> m (Either r (c (Leaf c m r)))
inspectLeaf = fmap (second fsumOnly) . inspect

-- | Initiate a connection on /some/ channel.
--
-- In practice, it is almost always preferable to use 'connectOn', or
-- specialised versions ('yieldOn', 'awaitOn').
connect :: (All Functor cs, Inductive cs) => FSum cs r -> Node cs m r
{-# INLINE connect #-}
connect con = Connect $ fmap Return con

-- | Initiate a connection on a channel specified by an index.
--
-- ====__Signatures for some specific indices__
-- @
-- 'connectOn' 'i0' :: 'Functor' c0 => c0 r -> 'Node' (c0 : cs) m r
-- 'connectOn' 'i1' :: 'Functor' c1 => c1 r -> 'Node' (c0 : c1 : cs) m r
-- 'connectOn' 'i2' :: 'Functor' c2 => c2 r -> 'Node' (c0 : c1 : c2 : cs) m r
-- @
--
-- ====__Examples of specialised types__
-- 'connectOn' can be specialised to any of the following types (and
-- more; these are just examples):
--
-- @
-- 'connectOn' 'i0' :: (a, r) -> 'Node' '['Yielding' a] m r
-- 'connectOn' 'i0' :: (a -> r) -> 'Node' '['Awaiting' a] m r
-- 'connectOn' 'i0' :: (a -> r) -> 'Node' '['Awaiting' a, 'Yielding' b, 'Awaiting' c] m r
-- 'connectOn' 'i3' :: (a, r) -> 'Node' '[f0, f1, f2, 'Yielding' a, f4] m r
-- @
connectOn :: (Functor c, Inductive cs) => IIndex n cs c -> c r -> Node cs m r
{-# INLINE connectOn #-}
connectOn n con = Connect $ finjectIdx n $ fmap Return con

-- | Provide a value on a channel specified by an index.
--
-- ====__Signatures for some specific indices__
-- @
-- 'yieldOn' 'i0' :: a -> 'Node' ('Yielding' a : cs) m ()
-- 'yieldOn' 'i1' :: a -> 'Node' (c0 : 'Yielding' a : cs) m ()
-- 'yieldOn' 'i2' :: a -> 'Node' (c0 : c1 : 'Yielding' a : cs) m ()
-- @
yieldOn :: Inductive cs => IIndex n cs (Yielding a) -> a -> Node cs m ()
{-# INLINE yieldOn #-}
yieldOn n a = connectOn n (a, ())

-- | Yield all elements of a container on a specified channel.
--
-- __See also__: 'yieldOn'
eachOn ::
     (Functor m, All Functor cs, Inductive cs, Foldable f)
  => IIndex n cs (Yielding a)
  -> f a
  -> Node cs m ()
{-# INLINE eachOn #-}
eachOn n = traverse_ (yieldOn n)

-- | Receive a value on a channel specified by an index.
--
-- ====__Signatures for some specific indices__
-- @
-- 'awaitOn' 'i0' :: 'Node' ('Awaiting' a : cs) m a
-- 'awaitOn' 'i1' :: 'Node' (c0 : 'Awaiting' a : cs) m a
-- 'awaitOn' 'i2' :: 'Node' (c0 : c1 : 'Awaiting' a : cs) m a
-- @
awaitOn :: Inductive cs => IIndex n cs (Awaiting a) -> Node cs m a
{-# INLINE awaitOn #-}
awaitOn n = connectOn n id

-- | Run an entire 'Leaf' within a bigger (in terms of channels)
-- 'Node', by identifying 'Leaf's sole channel with one of the
-- 'Node' channels.
--
-- ====__Signatures for some specific indices__
-- @
-- 'leafOn' 'i0' :: 'Functor' m => 'Leaf' c0 m r -> 'Node' (c0 : cs) m r
-- 'leafOn' 'i1' :: 'Functor' m => 'Leaf' c1 m r -> 'Node' (c0 : c1 : cs) m r
-- 'leafOn' 'i2' :: 'Functor' m => 'Leaf' c2 m r -> 'Node' (c0 : c1 : c2 : cs) m r
-- @
leafOn ::
     (Functor m, Functor c, Inductive cs)
  => IIndex n cs c
  -> Leaf c m r
  -> Node cs m r
leafOn n = gmapAll (finjectIdx n . fsumOnly)

-- | Transform entire list of channels of a 'Node' via a natural
-- transformation of their 'FSum'.
gmapAll ::
     (Functor m, All Functor cs, Inductive cs)
  => (forall x. FSum cs x -> FSum cs' x) -- ^ Convert communications
     -- on old channels into communications on new ones.
  -> Node cs m r -- ^ Node with an old list of channels.
  -> Node cs' m r -- ^ Same node, but with transformed communications.
gmapAll = transformCons

-- | Transform a single channel of a 'Node' via a natural transformation.
--
-- ====__Signatures for some specific indices__
-- @
-- 'gmapOn' 'i0' ::
--       ('Functor' m, 'Functor' c, 'All' 'Functor' cs)
--    => (forall x. c x -> c' x)
--    -> 'Node' (c : cs) m r
--    -> 'Node' (c' : cs) m r
--
-- 'gmapOn' 'i1' ::
--       ('Functor' m, 'Functor' c0, 'Functor' c1, 'All' 'Functor' cs)
--    => (forall x. c1 x -> c' x)
--    -> 'Node' (c0 : c1 : cs) m r
--    -> 'Node' (c0 : c' : cs) m r
--
-- 'gmapOn' 'i2' ::
--       ('Functor' m, 'Functor' c0, 'Functor' c1, 'Functor' c2, 'All' 'Functor' cs)
--    => (forall x. c2 x -> c' x)
--    -> 'Node' (c0 : c1 : c2 : cs) m r
--    -> 'Node' (c0 : c1 : c' : cs) m r
-- @
gmapOn ::
     (Functor m, All Functor cs, Replace n cs c' cs')
  => IIndex n cs c -- ^ An index of a channel to be replaced.
  -> (forall x. c x -> c' x) -- ^ A natural transformation to apply
     -- to the channel.
  -> Node cs m r -- ^ A 'Node' with an old channel.
  -> Node cs' m r -- ^ The same 'Node', but the channel in question is
     -- replaced by a new one.
gmapOn n f = gmapAll (freplaceIdx n f)

-- | Transform a single channel of a 'Node', with possible effects in
-- the base monad outside of a new channel functor.
--
-- ====__Signatures for some specific indices__
-- @
-- 'gmapOnM' 'i0' ::
--       ('Functor' m, 'Functor' c, 'All' 'Functor' cs)
--    => (forall x. c x -> m (c' x))
--    -> 'Node' (c : cs) m r
--    -> 'Node' (c' : cs) m r
--
-- 'gmapOnM' 'i1' ::
--       ('Functor' m, 'Functor' c0, 'Functor' c1, 'All' 'Functor' cs)
--    => (forall x. c1 x -> m (c' x))
--    -> 'Node' (c0 : c1 : cs) m r
--    -> 'Node' (c0 : c' : cs) m r
--
-- 'gmapOnM' 'i2' ::
--       ('Functor' m, 'Functor' c0, 'Functor' c1, 'Functor' c2, 'All' 'Functor' cs)
--    => (forall x. c2 x -> m (c' x))
--    -> 'Node' (c0 : c1 : c2 : cs) m r
--    -> 'Node' (c0 : c1 : c' : cs) m r
-- @
gmapOnM ::
     forall m cs cs' n c' r c. (Functor m, All Functor cs, Replace n cs c' cs')
  => IIndex n cs c -- ^ An index of a channel to be replaced.
  -> (forall x. c x -> m (c' x)) -- ^ A natural transformation to
     -- apply to the channel.
  -> Node cs m r
  -> Node cs' m r
gmapOnM n f = cata Return alg Effect
  where
    alg con =
      case fdecompReplaceIdx n (Proxy :: Proxy c') con of
        Right c ->
          Effect (fmap (Connect . finjectIdx (replaceIdx n)) (f c))
        Left c -> Connect c

-- | Transform a single channel of a 'Node', with possible monadic
-- effects inside a new channel functor.
--
-- ====__Signatures for some specific indices__
-- @
-- 'gmapOnM'' 'i0' ::
--       ('Functor' m, 'Functor' c, 'All' 'Functor' cs)
--    => (forall x. c x -> c' (m x))
--    -> 'Node' (c : cs) m r
--    -> 'Node' (c' : cs) m r
--
-- 'gmapOnM'' 'i1' ::
--       ('Functor' m, 'Functor' c0, 'Functor' c1, 'All' 'Functor' cs)
--    => (forall x. c1 x -> c' (m x))
--    -> 'Node' (c0 : c1 : cs) m r
--    -> 'Node' (c0 : c' : cs) m r
--
-- 'gmapOnM'' 'i2' ::
--       ('Functor' m, 'Functor' c0, 'Functor' c1, 'Functor' c2, 'All' 'Functor' cs)
--    => (forall x. c2 x -> c' (m x))
--    -> 'Node' (c0 : c1 : c2 : cs) m r
--    -> 'Node' (c0 : c1 : c' : cs) m r
-- @
gmapOnM' ::
     (Functor m, All Functor cs, Functor c', Replace n cs c' cs')
  => IIndex n cs c -- ^ An index of a channel to be replaced.
  -> (forall x. c x -> c' (m x)) -- ^ A natural transformation to
     -- apply to the channel.
  -> Node cs m r
  -> Node cs' m r
gmapOnM' n f = transformCons (freplaceIdx n (fmap Effect . f))

-- | Transform an outgoing stream of values on a specified channel.
--
-- @
-- 'mapOn' n f = 'gmapOn' n (\\(a, x) -> (f a, x))
-- @
--
-- ====__Signatures for some specific indices__
-- @
-- 'mapOn' 'i0' ::
--      ('Functor' m, 'All' 'Functor' cs)
--   => (a -> b)
--   -> 'Node' ('Yielding' a : cs) m r
--   -> 'Node' ('Yielding' b : cs) m r
--
-- 'mapOn' 'i1' ::
--      ('Functor' m, 'Functor' c0, 'All' 'Functor' cs)
--   => (a -> b)
--   -> 'Node' (c0 : 'Yielding' a : cs) m r
--   -> 'Node' (c0 : 'Yielding' b : cs) m r
--
-- 'mapOn' 'i2' ::
--      ('Functor' m, 'Functor' c0, 'Functor' c1, 'All' 'Functor' cs)
--   => (a -> b)
--   -> 'Node' (c0 : c1 : 'Yielding' a : cs) m r
--   -> 'Node' (c0 : c1 : 'Yielding' b : cs) m r
-- @
mapOn ::
     (Functor m, All Functor cs, Replace n cs (Yielding b) cs')
  => IIndex n cs (Yielding a) -- ^ An index of a channel to be mapped over.
  -> (a -> b) -- ^ A function to apply to outgoing elements.
  -> Node cs m r -- ^ An old 'Node'.
  -> Node cs' m r -- ^ Same node, but with the channel replaced.
mapOn n f = gmapOn n (first f)

-- | Transform an outgoing stream of values, with possible effects in
-- the base monad along the way.
--
-- ====__Signatures for some specific indices__
-- @
-- 'mapOnM' 'i0' ::
--      ('Functor' m, 'All' 'Functor' cs)
--   => (a -> m b)
--   -> 'Node' ('Yielding' a : cs) m r
--   -> 'Node' ('Yielding' b : cs) m r
--
-- 'mapOnM' 'i1' ::
--      ('Functor' m, 'Functor' c0, 'All' 'Functor' cs)
--   => (a -> m b)
--   -> 'Node' (c0 : 'Yielding' a : cs) m r
--   -> 'Node' (c0 : 'Yielding' b : cs) m r
--
-- 'mapOnM' 'i2' ::
--      ('Functor' m, 'Functor' c0, 'Functor' c1, 'All' 'Functor' cs)
--   => (a -> m b)
--   -> 'Node' (c0 : c1 : 'Yielding' a : cs) m r
--   -> 'Node' (c0 : c1 : 'Yielding' b : cs) m r
-- @
mapOnM ::
     (Functor m, All Functor cs, Replace n cs (Yielding b) cs')
  => IIndex n cs (Yielding a) -- ^ An index of a channel to be mapped over.
  -> (a -> m b) -- ^ A function to apply to outgoing elements.
  -> Node cs m r -- ^ An old 'Node'.
  -> Node cs' m r -- ^ Same node, but with channel replaced.
mapOnM n f = gmapOnM n (\(a, x) -> fmap (, x) (f a))

-- | Transform an incoming stream of values on a specified channel.
--
-- @
-- 'contramapOn' n f = 'gmapOn' n (\\g -> g . f)
-- @
--
-- ====__Signatures for some specific indices__
-- @
-- 'contramapOn' 'i0' ::
--      ('Functor' m, 'All' 'Functor' cs)
--   => (b -> a)
--   -> 'Node' ('Awaiting' a : cs) m r
--   -> 'Node' ('Awaiting' b : cs) m r
--
-- 'contramapOn' 'i1' ::
--      ('Functor' m, 'Functor' c0, 'All' 'Functor' cs)
--   => (b -> a)
--   -> 'Node' (c0 : 'Awaiting' a : cs) m r
--   -> 'Node' (c0 : 'Awaiting' b : cs) m r
--
-- 'contramapOn' 'i2' ::
--      ('Functor' m, 'Functor' c0, 'Functor' c1, 'All' 'Functor' cs)
--   => (b -> a)
--   -> 'Node' (c0 : c1 : 'Awaiting' a : cs) m r
--   -> 'Node' (c0 : c1 : 'Awaiting' b : cs) m r
-- @
contramapOn ::
     (Functor m, All Functor cs, Replace n cs (Awaiting b) cs')
  => IIndex n cs (Awaiting a) -- ^ Index of the channel to be mapped
                              -- over.
  -> (b -> a) -- ^ The function to transform values received by a new
     -- 'Node' into the ones requested by the old one.
  -> Node cs m r -- ^ Original 'Node'.
  -> Node cs' m r -- ^ Same 'Node', but with the channel replaced.
contramapOn n f = gmapOn n (. f)

-- | Transform an incoming stream of values, with some effects in the
-- base monad along the way.
--
-- ====__Signatures for some specific indices__
-- @
-- 'contramapOnM' 'i0' ::
--      ('Functor' m, 'All' 'Functor' cs)
--   => (b -> m a)
--   -> 'Node' ('Awaiting' a : cs) m r
--   -> 'Node' ('Awaiting' b : cs) m r
--
-- 'contramapOnM' 'i1' ::
--      ('Functor' m, 'Functor' c0, 'All' 'Functor' cs)
--   => (b -> m a)
--   -> 'Node' (c0 : 'Awaiting' a : cs) m r
--   -> 'Node' (c0 : 'Awaiting' b : cs) m r
--
-- 'contramapOnM' 'i2' ::
--      ('Functor' m, 'Functor' c0, 'Functor' c1, 'All' 'Functor' cs)
--   => (b -> m a)
--   -> 'Node' (c0 : c1 : 'Awaiting' a : cs) m r
--   -> 'Node' (c0 : c1 : 'Awaiting' b : cs) m r
-- @
contramapOnM ::
     (Applicative m, All Functor cs, Replace n cs (Awaiting b) cs')
  => IIndex n cs (Awaiting a) -- ^ Index of the channel to be mapped
                              -- over.
  -> (b -> m a) -- ^ The function to transform values received by a new
     -- 'Node' into the ones requested by the old one.
  -> Node cs m r -- ^ Original 'Node'.
  -> Node cs' m r -- ^ Same 'Node', but with the channel replaced.
contramapOnM n f = gmapOnM' n (\g -> fmap g . f)

-- | Replace the current list of channels by substituting a
-- computation with new channels for each communication attempt.
--
-- Essentially, @'gforAll' node body@ replaces each call to 'connect'
-- (as well as specialised variants) with @body@.
gforAll ::
     (Functor m, All Functor cs, Inductive cs, All Functor cs', Inductive cs')
  => Node cs m r
  -> (forall x. FSum cs x -> Node cs' m x)
  -> Node cs' m r
gforAll node f = cata Return (join . f) Effect node

-- | Substitute each attempt to communicate on a given channel with a
-- computation with a different list of channels.
--
-- The net result of @'gforOn' n node body@ is as if each instance of
-- @'connectOn' n@ in @node@ (including specialisations, such as
-- 'yieldOn' or 'awaitOn') was replaced by the @body@, with all
-- indices in other connection suitably modified to fit new channel list.
--
-- ====__Signatures for some specific indices__
-- @
-- 'gforOn' 'i0' ::
--       ( 'Functor' m, 'Functor' c, 'All' 'Functor' cs, 'All 'Functor' cs'
--       , 'Known' 'Length' cs)
--    => 'Node' (c : cs) m r
--    -> (forall x. c x -> 'Node' cs' m x)
--    -> 'Node' (cs 'Type.Family.List.++' cs') m r
--
-- 'gforOn' 'i1' ::
--       ( 'Functor' m, 'Functor' c0, 'Functor' c1
--       , 'All' 'Functor' cs, 'All' 'Functor' cs'
--       , 'Known' 'Length' cs)
--    => 'Node' (c0 : c1 : cs) m r
--    -> (forall x. c1 x -> 'Node' cs' m x)
--    -> Node ((c0 : cs) 'Type.Family.List.++' cs') m r
--
-- 'gforOn' 'i2' ::
--       ( 'Functor' m, 'Functor' c0, 'Functor' c1, 'Functor' c2
--       , 'All' 'Functor' cs, 'All' 'Functor' cs'
--       , 'Known' 'Length' cs)
--    => 'Node' (c0 : c1 : c2 : cs) m r
--    -> (forall x. c2 x -> 'Node' cs' m x)
--    -> 'Node' ((c0 : c1 : cs) 'Type.Family.List.++' cs') m r
-- @
gforOn ::
     forall m n cs ocs cs' rescs r c.
     ( Functor m
     , All Functor cs
     , Remove n cs ocs
     , Append ocs cs' rescs
     , All Functor cs'
     )
  => IIndex n cs c -- ^ A channel over which to loop.
  -> Node cs m r -- ^ A source of communication requests to loop over.
  -> (forall x. c x -> Node cs' m x) -- ^ Loop body.
  -> Node rescs m r
gforOn idx node f =
  gforOn_ idx node f \\
  appendAll
    (Proxy :: Proxy Functor)
    (Proxy :: Proxy ocs)
    (Proxy :: Proxy cs') \\
  iwithoutRetainsAll (Proxy :: Proxy Functor) idx

gforOn_ ::
     forall m n cs ocs cs' rescs r c.
     ( Functor m
     , All Functor cs
     , Remove n cs ocs
     , All Functor ocs
     , All Functor cs'
     , All Functor rescs
     , Append ocs cs' rescs
     )
  => IIndex n cs c
  -> Node cs m r
  -> (forall x. c x -> Node cs' m x)
  -> Node rescs m r
gforOn_ n node f = gforAll node body
  where
    body con =
      case fdecompIdx n con of
        Left other -> connect (finl proxyInner other)
        Right c -> gmapAll (finr proxyOuter) (f c)
    proxyInner :: Proxy cs'
    proxyInner = Proxy
    proxyOuter :: Proxy ocs
    proxyOuter = Proxy

-- | Substitute each attempt to communicate on a specified channel
-- with a computation with a different open channel.
--
-- The primary difference from 'gforOn' is that the new channel is
-- substituted for the old one, instead of being appended at the end,
-- which makes this function more suitable for per-channel
-- transformations.
--
-- ====__Signatures for some specific indices__
-- @
-- 'gforOnLeaf' 'i0' ::
--       ('Functor' m, 'Functor' c, 'Functor' c', 'All' 'Functor' cs)
--    => 'Node' (c : cs) m r
--    -> (forall x. c x -> 'Leaf' c' m x)
--    -> 'Node' (c' : cs) m r
--
-- 'gforOnLeaf' 'i1' ::
--       ('Functor' m, 'Functor' c0, 'Functor' c1, 'Functor' c', 'All' 'Functor' cs)
--    => 'Node' (c0 : c1 : cs) m r
--    -> (forall x. c1 x -> 'Leaf' c' m x)
--    -> 'Node' (c0 : c' : cs) m r
--
-- 'gforOnLeaf' 'i2' ::
--       ( 'Functor' m, 'Functor' c0, 'Functor' c1, 'Functor' c2, 'Functor' c'
--       , 'All' 'Functor' cs)
--    => 'Node' (c0 : c1 : c2 : cs) m r
--    -> (forall x. c2 x -> 'Leaf' c' m x)
--    -> 'Node' (c0 : c1 : c' : cs) m r
-- @
gforOnLeaf ::
     forall m n cs cs' c' r c.
     (Functor m, All Functor cs, Functor c', Replace n cs c' cs')
  => IIndex n cs c -- ^ A channel over which to loop.
  -> Node cs m r -- ^ A source of communication requests to loop over.
  -> (forall x. c x -> Leaf c' m x) -- ^ Loop body.
  -> Node cs' m r
gforOnLeaf n node f =
  gforOnLeaf_ n node f \\
  ireplacedRetainsAll (Proxy :: Proxy c') (Proxy :: Proxy Functor) n

gforOnLeaf_ ::
     forall m n cs c' cs' r c.
     ( Functor m
     , All Functor cs
     , Functor c'
     , Replace n cs c' cs'
     , All Functor cs'
     )
  => IIndex n cs c
  -> Node cs m r
  -> (forall x. c x -> Leaf c' m x)
  -> Node cs' m r
gforOnLeaf_ n node f = gforAll node body
  where
    body con =
      case fdecompReplaceIdx n (Proxy :: Proxy c') con of
        Left c -> connect c
        Right c -> gmapAll (finjectIdx newIdx . fsumOnly) (f c)
    newIdx = replaceIdx n

-- | Loop over a 'Node', replacing each 'yieldOn' the specified
-- channel with a computation with a different list of channels.
--
-- This is merely a specialisation of 'gforOn' for 'Yielding'.
--
-- ====__Signatures for some specific indices__
-- @
-- 'forOn' 'i0' ::
--      ( 'Functor' m, 'All' 'Functor' cs, 'All' 'Functor' cs'
--      , 'Known' 'Length' cs)
--   => 'Node' ('Yielding' a : cs) m r
--   -> (a -> 'Node' cs' m r)
--   -> 'Node' (cs 'Type.Family.List.++' cs') m r
--
-- 'forOn' 'i1' ::
--      ( 'Functor' m, 'Functor' c0
--      , 'All' 'Functor' cs, 'All' 'Functor' cs'
--      , 'Known' 'Length' cs)
--   => 'Node' (c0 : 'Yielding' a : cs) m r
--   -> (a -> 'Node' cs' m ())
--   -> 'Node' ((c0 : cs) 'Type.Family.List.++' cs') m r
--
-- 'forOn' 'i2' ::
--      ( 'Functor' m, 'Functor' c0, 'Functor' c1
--      , 'All' 'Functor' cs, 'All' 'Functor' cs'
--      , 'Known' 'Length' cs)
--   => 'Node' (c0 : c1 : 'Yielding' a : cs) m r
--   -> (a -> 'Node' cs' m ())
--   -> 'Node' ((c0 : c1 : cs) 'Type.Family.List.++' cs') m r
-- @
forOn ::
     ( Functor m
     , All Functor cs
     , All Functor cs'
     , Remove n cs ocs
     , Append ocs cs' rescs
     )
  => IIndex n cs (Yielding a) -- ^ A channel over which to loop.
  -> Node cs m r -- ^ A source of values to loop over.
  -> (a -> Node cs' m ()) -- ^ Loop body.
  -> Node rescs m r
forOn n node f = gforOn n node (\(a, r) -> r <$ f a)

-- | Same as 'forOn', but new channel is substituted in-place for the
-- old one.
--
-- ====__Signatures for some specific indices__
-- @
-- 'forOnLeaf' 'i0' ::
--       ('Functor' m, 'Functor' c, 'All' 'Functor' cs)
--    => 'Node' ('Yielding' a : cs) m r
--    -> (a -> 'Leaf' c m ())
--    -> 'Node' (c : cs) m r
--
-- 'forOnLeaf' 'i1' ::
--       ('Functor' m, 'Functor' c0, 'Functor' c, 'All' 'Functor' cs)
--    => 'Node' (c0 : 'Yielding' a : cs) m r
--    -> (a -> 'Leaf' c m ())
--    -> 'Node' (c0 : c : cs) m r
--
-- 'forOnLeaf' 'i2' ::
--       ('Functor' m, 'Functor' c0, 'Functor' c1, 'Functor' c, 'All' 'Functor' cs)
--    => 'Node' (c0 : c1 : 'Yielding' a : cs) m r
--    -> (a -> 'Leaf' c m ())
--    -> 'Node' (c0 : c1 : c : cs) m r
-- @
forOnLeaf ::
     (Functor m, All Functor cs, Functor c, Replace n cs c cs')
  => IIndex n cs (Yielding a) -- ^ A channel over which to loop.
  -> Node cs m r -- ^ A source of values to loop over.
  -> (a -> Leaf c m ()) -- ^ Loop body.
  -> Node cs' m r
forOnLeaf n node f = gforOnLeaf n node (\(a, r) -> r <$ f a)

-- | Loop over a 'Node', replacing each 'awaitOn' the specified
-- channel by the loop body, which should provide the value asked for.
--
-- This is merely a specialisation of 'gforOn' for 'Awaiting'.
--
-- ====__Signatures for some specific indices__
-- @
-- 'contraforOn' 'i0' ::
--       ( 'Functor' 'm', 'All' 'Functor' cs, 'All' 'Functor' cs'
--       , 'Known' 'Length' cs)
--    => 'Node' ('Awaiting' a : cs) m r
--    -> 'Node' cs' m a
--    -> 'Node' (cs 'Type.Family.List.++' cs') m r
--
-- 'contraforOn' 'i1' ::
--       ( 'Functor' 'm', 'Functor' c0
--       , 'All' 'Functor' cs, 'All' 'Functor' cs'
--       , 'Known' 'Length' cs)
--    => 'Node' (c0 : 'Awaiting' a : cs) m r
--    -> 'Node' cs' m a
--    -> 'Node' ((c0 : cs) 'Type.Family.List.++' cs') m r
--
-- 'contraforOn' 'i2' ::
--       ( 'Functor' 'm', 'Functor' c0, 'Functor' c1
--       , 'All' 'Functor' cs, 'All' 'Functor' cs'
--       , 'Known' 'Length' cs)
--    => 'Node' (c0 : c1 : 'Awaiting' a : cs) m r
--    -> 'Node' cs' m a
--    -> 'Node' ((c0 : c1 : cs) 'Type.Family.List.++' cs') m r
-- @
contraforOn ::
     ( Remove n cs ocs
     , Functor m
     , All Functor cs'
     , All Functor cs
     , Append ocs cs' rescs
     )
  => IIndex n cs (Awaiting a) -- ^ A channel over which to loop.
  -> Node cs m r -- ^ A receiver of values.
  -> Node cs' m a -- ^ A provider of values, run once for each
                  -- 'awaitOn'.
  -> Node rescs m r
contraforOn n node body = gforOn n node (<$> body)

-- | Same as 'contraforOn', but new channel is substituted in-place for the
-- old one.
--
-- ====__Signatures for some specific indices__
-- @
-- 'contraforOnLeaf' 'i0' ::
--       ('Functor' m, 'Functor' c, 'All' 'Functor' cs)
--    => 'Node' ('Awaiting' a : cs) m r
--    -> 'Leaf' c m a
--    -> 'Node' (c : cs) m r
--
-- 'contraforOnLeaf' 'i1' ::
--       ('Functor' m, 'Functor' c0, 'Functor' c, 'All' 'Functor' cs)
--    => 'Node' (c0 : 'Awaiting' a : cs) m r
--    -> 'Leaf' c m a
--    -> 'Node' (c0 : c : cs) m r
--
-- 'contraforOnLeaf' 'i2' ::
--       ('Functor' m, 'Functor' c0, 'Functor' c1, 'Functor' c, 'All' 'Functor' cs)
--    => 'Node' (c0 : c1 : 'Awaiting' a : cs) m r
--    -> 'Leaf' c m a
--    -> 'Node' (c0 : c1 : c : cs) m r
-- @
contraforOnLeaf ::
     (Functor m, All Functor cs, Functor c, Replace n cs c cs')
  => IIndex n cs (Awaiting a) -- ^ A channel over which to loop.
  -> Node cs m r -- ^ A receiver of values.
  -> Leaf c m a -- ^ A provider of values, run once for each 'awaitOn'.
  -> Node cs' m r
contraforOnLeaf n node body = gforOnLeaf n node (<$> body)

-- $indices
--
-- Many functions operating on 'Node's require one or more indices
-- indicating the communication channels over which to perform the
-- operation.  Due to all the type-level machinery involved, the
-- indices have to be of a very specific type, that ties together the
-- actual value of the index, the list it's indexing into, and the
-- element at that index.
--
-- However, typically, when operating on 'Node's with known “shapes”
-- on known channels, it is possible to ignore all that nuance and
-- simply use an appropriate index from this section.
