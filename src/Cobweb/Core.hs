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
  , Leaf
  , Yielding
  , Awaiting
    -- * Running 'Node'
  , run
  , inspect
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
  , connects
  , connectsOn
  , yieldOn
  , eachOn
  , awaitOn
    -- * Maps
  , mapsAll
  , mapsOn
  , mapsOnM
  , mapsOnM'
  , mapOn
  , mapOnM
  , premapOn
  , premapOnM
    -- * Looping over 'Node's
  , forsOn
  , forOn
  , preforOn
  ) where

import Control.Monad (join)
import Data.Bifunctor (first)
import Data.Foldable (traverse_)
import Data.Functor.Foldable (Recursive(cata))
import Data.Proxy (Proxy(Proxy))
import Data.Type.Length (Length)
import Data.Type.Sum.Lifted (FSum, nilFSum)
import Data.Void (absurd)
import Type.Class.Known (Known)
import Type.Class.Witness ((:-), Witness((\\)))
import Type.Family.List (type (++))

import Cobweb.Internal
       (Node(Node, getNode), NodeF(ConnectF, EffectF, ReturnF), inspect,
        transform, transformCons, unfold)
import Cobweb.Type.Combinators
       (All, IIndex, IReplace, IReplaced, IWithout, fdecompIdx,
        fdecompReplaceIdx, finjectIdx, finl, finr, freplaceIdx, i0, i1,
        i10, i2, i3, i4, i5, i6, i7, i8, i9, ireplace, replaceIdx)
import Cobweb.Type.Lemmata (appendAll, iwithoutRetainsAll)

-- | A node with no channels, isomorphic to an effect in the base monad.
--
-- __See also__: 'run'
type Effect = Node '[]

-- | A node with only one channel.
type Leaf c = Node '[ c]

-- | A channel type of @'Yielding' a@ implies that a 'Node' is
-- producing values of type @a@ on this channel.
--
-- __See also__: 'yieldOn', "Cobweb.Producer"
type Yielding = (,)

-- | A channel type of @'Awaiting' a@ implies that a 'Node' is
-- receiving values of type @a@ on this channel.
--
-- __See also__: 'awaitOn', "Cobweb.Consumer"
type Awaiting = (->)

-- | Run a node with no open channels in the base monad.
run :: Monad m => Effect m r -> m r
run = cata alg
  where
    alg (ReturnF r) = pure r
    alg (EffectF eff) = join eff
    alg (ConnectF con) = absurd (nilFSum con)

-- | Initiate a connection on /some/ channel.
--
-- In practice, it is almost always preferable to use 'connectsOn', or
-- specialised versions ('yieldOn', 'awaitOn').
connects :: All Functor cs => FSum cs r -> Node cs m r
connects con = Node $ ConnectF $ fmap (Node . ReturnF) con

-- | Initiate a connection on a channel specified by an index.
--
-- ====__Signatures for some specific indices__
-- @
-- 'connectsOn' 'i0' :: 'Functor' c0 => c0 r -> 'Node' (c0 : cs) m r
-- 'connectsOn' 'i1' :: 'Functor' c1 => c1 r -> 'Node' (c0 : c1 : cs) m r
-- 'connectsOn' 'i2' :: 'Functor' c2 => c2 r -> 'Node' (c0 : c1 : c2 : cs) m r
-- @
--
-- ====__Examples of specialised types__
-- 'connectsOn' can be specialised to any of the following types (and
-- more; these are just examples):
--
-- @
-- 'connectsOn' 'i0' :: (a, r) -> 'Node' '['Yielding' a] m r
-- 'connectsOn' 'i0' :: (a -> r) -> 'Node' '['Awaiting' a] m r
-- 'connectsOn' 'i0' :: (a -> r) -> 'Node' '['Awaiting' a, 'Yielding' b, 'Awaiting' c] m r
-- 'connectsOn' 'i3' :: (a, r) -> 'Node' '[f0, f1, f2, 'Yielding' a, f4] m r
-- @
connectsOn :: Functor c => IIndex n cs c -> c r -> Node cs m r
connectsOn n con = Node $ ConnectF $ finjectIdx n $ fmap (Node . ReturnF) con

-- | Provide a value on a channel specified by an index.
--
-- ====__Signatures for some specific indices__
-- @
-- 'yieldOn' 'i0' :: a -> 'Node' ('Yielding' a : cs) m ()
-- 'yieldOn' 'i1' :: a -> 'Node' (c0 : 'Yielding' a : cs) m ()
-- 'yieldOn' 'i2' :: a -> 'Node' (c0 : c1 : 'Yielding' a : cs) m ()
-- @
yieldOn :: IIndex n cs (Yielding a) -> a -> Node cs m ()
yieldOn n a = connectsOn n (a, ())

-- | Yield all elements of a container on a specified channel.
--
-- __See also__: 'yieldOn'
eachOn ::
     (Functor m, All Functor cs, Foldable f)
  => IIndex n cs (Yielding a)
  -> f a
  -> Node cs m ()
eachOn n = traverse_ (yieldOn n)

-- | Receive a value on a channel specified by an index.
--
-- ====__Signatures for some specific indices__
-- @
-- 'awaitOn' 'i0' :: 'Node' ('Awaiting' a : cs) m a
-- 'awaitOn' 'i1' :: 'Node' (c0 : 'Awaiting' a : cs) m a
-- 'awaitOn' 'i2' :: 'Node' (c0 : c1 : 'Awaiting' a : cs) m a
-- @
awaitOn :: IIndex n cs (Awaiting a) -> Node cs m a
awaitOn n = connectsOn n id

-- | Transform entire list of channels of a 'Node' via a natural
-- transformation of their 'FSum'.
mapsAll ::
     (Functor m, All Functor cs)
  => (forall x. FSum cs x -> FSum cs' x) -- ^ Convert communications
     -- on old channels into communications on new ones.
  -> Node cs m r -- ^ Node with an old list of channels.
  -> Node cs' m r -- ^ Same node, but with transformed communications.
mapsAll = transformCons

-- | Transform a single channel of a 'Node' via a natural transformation.
--
-- ====__Signatures for some specific indices__
-- @
-- 'mapsOn' 'i0' ::
--       ('Functor' m, 'Functor' c, 'All' 'Functor' cs)
--    => (forall x. c x -> c' x)
--    -> 'Node' (c : cs) m r
--    -> 'Node' (c' : cs) m r
--
-- 'mapsOn' 'i1' ::
--       ('Functor' m, 'Functor' c0, 'Functor' c1, 'All' 'Functor' cs)
--    => (forall x. c1 x -> c' x)
--    -> 'Node' (c0 : c1 : cs) m r
--    -> 'Node' (c0 : c' : cs) m r
--
-- 'mapsOn' 'i2' ::
--       ('Functor' m, 'Functor' c0, 'Functor' c1, 'Functor' c2, 'All' 'Functor' cs)
--    => (forall x. c2 x -> c' x)
--    -> 'Node' (c0 : c1 : c2 : cs) m r
--    -> 'Node' (c0 : c1 : c' : cs) m r
-- @
mapsOn ::
     (Functor m, All Functor cs, IReplaced n cs c' cs')
  => IIndex n cs c -- ^ An index of a channel to be replaced.
  -> (forall x. c x -> c' x) -- ^ A natural transformation to apply
     -- to the channel.
  -> Node cs m r -- ^ A 'Node' with an old channel.
  -> Node cs' m r -- ^ The same 'Node', but the channel in question is
     -- replaced by a new one.
mapsOn n f = mapsAll (freplaceIdx n f)

-- | Transform a single channel of a 'Node', with possible effects in
-- the base monad outside of a new channel functor.
--
-- ====__Signatures for some specific indices__
-- @
-- 'mapsOnM' 'i0' ::
--       ('Functor' m, 'Functor' c, 'All' 'Functor' cs)
--    => (forall x. c x -> m (c' x))
--    -> 'Node' (c : cs) m r
--    -> 'Node' (c' : cs) m r
--
-- 'mapsOnM' 'i1' ::
--       ('Functor' m, 'Functor' c0, 'Functor' c1, 'All' 'Functor' cs)
--    => (forall x. c1 x -> m (c' x))
--    -> 'Node' (c0 : c1 : cs) m r
--    -> 'Node' (c0 : c' : cs) m r
--
-- 'mapsOnM' 'i2' ::
--       ('Functor' m, 'Functor' c0, 'Functor' c1, 'Functor' c2, 'All' 'Functor' cs)
--    => (forall x. c2 x -> m (c' x))
--    -> 'Node' (c0 : c1 : c2 : cs) m r
--    -> 'Node' (c0 : c1 : c' : cs) m r
-- @
mapsOnM ::
     forall m cs n c' cs' r c.
     (Functor m, All Functor cs, IReplaced n cs c' cs')
  => IIndex n cs c  -- ^ An index of a channel to be replaced.
  -> (forall x. c x -> m (c' x)) -- ^ A natural transformation to
     -- apply to the channel.
  -> Node cs m r
  -> Node cs' m r
mapsOnM n f = transform alg
  where
    alg (ReturnF r) = ReturnF r
    alg (EffectF eff) = EffectF eff
    alg (ConnectF con) =
      case fdecompReplaceIdx n (Proxy :: Proxy c') con of
        Right c ->
          EffectF
            (fmap
               (Node .
                ConnectF .
                finjectIdx (replaceIdx (ireplace :: IReplace n cs c' cs')))
               (f c))
        Left c -> ConnectF c

-- | Transform a single channel of a 'Node', with possible monadic
-- effects inside a new channel functor.
--
-- ====__Signatures for some specific indices__
-- @
-- 'mapsOnM'' 'i0' ::
--       ('Functor' m, 'Functor' c, 'All' 'Functor' cs)
--    => (forall x. c x -> c' (m x))
--    -> 'Node' (c : cs) m r
--    -> 'Node' (c' : cs) m r
--
-- 'mapsOnM'' 'i1' ::
--       ('Functor' m, 'Functor' c0, 'Functor' c1, 'All' 'Functor' cs)
--    => (forall x. c1 x -> c' (m x))
--    -> 'Node' (c0 : c1 : cs) m r
--    -> 'Node' (c0 : c' : cs) m r
--
-- 'mapsOnM'' 'i2' ::
--       ('Functor' m, 'Functor' c0, 'Functor' c1, 'Functor' c2, 'All' 'Functor' cs)
--    => (forall x. c2 x -> c' (m x))
--    -> 'Node' (c0 : c1 : c2 : cs) m r
--    -> 'Node' (c0 : c1 : c' : cs) m r
-- @
mapsOnM' ::
     (Functor m, All Functor cs, IReplaced n cs c' cs', Functor c')
  => IIndex n cs c -- ^ An index of a channel to be replaced.
  -> (forall x. c x -> c' (m x)) -- ^ A natural transformation to
     -- apply to the channel.
  -> Node cs m r
  -> Node cs' m r
mapsOnM' n f = transformCons (freplaceIdx n (fmap (Node . EffectF) . f))

-- | Transform an outgoing stream of values on a specified channel.
--
-- @
-- 'mapOn' n f = 'mapsOn' n (\\(a, x) -> (f a, x))
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
     (Functor m, All Functor cs, IReplaced n cs (Yielding b) cs')
  => IIndex n cs (Yielding a) -- ^ An index of a channel to be mapped over.
  -> (a -> b) -- ^ A function to apply to outgoing elements.
  -> Node cs m r -- ^ An old 'Node'.
  -> Node cs' m r -- ^ Same node, but with the channel replaced.
mapOn n f = mapsOn n (first f)

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
     (Functor m, All Functor cs, IReplaced n cs (Yielding b) cs')
  => IIndex n cs (Yielding a) -- ^ An index of a channel to be mapped over.
  -> (a -> m b) -- ^ A function to apply to outgoing elements.
  -> Node cs m r -- ^ An old 'Node'.
  -> Node cs' m r -- ^ Same node, but with channel replaced.
mapOnM n f = mapsOnM n (\(a, x) -> fmap (, x) (f a))

-- | Transform an incoming stream of values on a specified channel.
--
-- @
-- 'premapOn' n f = 'mapsOn' n (\\g -> g . f)
-- @
--
-- ====__Signatures for some specific indices__
-- @
-- 'premapOn' 'i0' ::
--      ('Functor' m, 'All' 'Functor' cs)
--   => (b -> a)
--   -> 'Node' ('Awaiting' a : cs) m r
--   -> 'Node' ('Awaiting' b : cs) m r
--
-- 'premapOn' 'i1' ::
--      ('Functor' m, 'Functor' c0, 'All' 'Functor' cs)
--   => (b -> a)
--   -> 'Node' (c0 : 'Awaiting' a : cs) m r
--   -> 'Node' (c0 : 'Awaiting' b : cs) m r
--
-- 'premapOn' 'i2' ::
--      ('Functor' m, 'Functor' c0, 'Functor' c1, 'All' 'Functor' cs)
--   => (b -> a)
--   -> 'Node' (c0 : c1 : 'Awaiting' a : cs) m r
--   -> 'Node' (c0 : c1 : 'Awaiting' b : cs) m r
-- @
premapOn ::
     (Functor m, All Functor cs, IReplaced n cs (Awaiting b) cs')
  => IIndex n cs (Awaiting a) -- ^ Index of the channel to be mapped
                              -- over.
  -> (b -> a) -- ^ The function to transform values received by a new
     -- 'Node' into the ones requested by the old one.
  -> Node cs m r -- ^ Original 'Node'.
  -> Node cs' m r -- ^ Same 'Node', but with the channel replaced.
premapOn n f = mapsOn n (. f)

-- | Transform an incoming stream of values, with some effects in the
-- base monad along the way.
--
-- ====__Signatures for some specific indices__
-- @
-- 'premapOnM' 'i0' ::
--      ('Functor' m, 'All' 'Functor' cs)
--   => (b -> m a)
--   -> 'Node' ('Awaiting' a : cs) m r
--   -> 'Node' ('Awaiting' b : cs) m r
--
-- 'premapOnM' 'i1' ::
--      ('Functor' m, 'Functor' c0, 'All' 'Functor' cs)
--   => (b -> m a)
--   -> 'Node' (c0 : 'Awaiting' a : cs) m r
--   -> 'Node' (c0 : 'Awaiting' b : cs) m r
--
-- 'premapOnM' 'i2' ::
--      ('Functor' m, 'Functor' c0, 'Functor' c1, 'All' 'Functor' cs)
--   => (b -> m a)
--   -> 'Node' (c0 : c1 : 'Awaiting' a : cs) m r
--   -> 'Node' (c0 : c1 : 'Awaiting' b : cs) m r
-- @
premapOnM ::
     (Applicative m, All Functor cs, IReplaced n cs (Awaiting b) cs')
  => IIndex n cs (Awaiting a) -- ^ Index of the channel to be mapped
                              -- over.
  -> (b -> m a) -- ^ The function to transform values received by a new
     -- 'Node' into the ones requested by the old one.
  -> Node cs m r -- ^ Original 'Node'.
  -> Node cs' m r -- ^ Same 'Node', but with the channel replaced.
premapOnM n f = mapsOnM' n (\g -> fmap g . f)

-- | Substitute each attempt to communicate on a given channel with a
-- computation with a different list of channels.
--
-- The net result of @'forsOn' n node body@ is as if each instance of
-- @'connectsOn' n@ in @node@ (including specialisations, such as
-- 'yieldOn' or 'awaitOn') was replaced by the @body@, with all
-- indices in other connection suitably modified to fit new channel list.
--
-- ====__Signatures for some specific indices__
-- @
-- 'forsOn' 'i0' ::
--       ( 'Functor' m, 'Functor' c, 'All' 'Functor' cs, 'All 'Functor' cs'
--       , 'Known' 'Length' cs)
--    => 'Node' (c : cs) m r
--    -> (forall x. c x -> 'Node' cs' m x)
--    -> 'Node' (cs 'Type.Family.List.++' cs') m r
--
-- 'forsOn' 'i1' ::
--       ( 'Functor' m, 'Functor' c0, 'Functor' c1
--       , 'All' 'Functor' cs, 'All' 'Functor' cs'
--       , 'Known' 'Length' cs)
--    => 'Node' (c0 : c1 : cs) m r
--    -> (forall x. c1 x -> 'Node' cs' m x)
--    -> Node ((c0 : cs) 'Type.Family.List.++' cs') m r
--
-- 'forsOn' 'i2' ::
--       ( 'Functor' m, 'Functor' c0, 'Functor' c1, 'Functor' c2
--       , 'All' 'Functor' cs, 'All' 'Functor' cs'
--       , 'Known' 'Length' cs)
--    => 'Node' (c0 : c1 : c2 : cs) m r
--    -> (forall x. c2 x -> 'Node' cs' m x)
--    -> 'Node' ((c0 : c1 : cs) 'Type.Family.List.++' cs') m r
-- @
forsOn ::
     forall m n cs cs' cs'' r c.
     ( Functor m
     , All Functor cs
     , IWithout n cs cs''
     , Known Length cs''
     , All Functor cs'
     )
  => IIndex n cs c -- ^ A channel over which to loop.
  -> Node cs m r -- ^ A source of communication requests to loop over.
  -> (forall x. c x -> Node cs' m x) -- ^ Loop body.
  -> Node (cs'' ++ cs') m r
forsOn idx node f =
  forsOn_ idx node f \\
  (appendAll (Proxy :: Proxy Functor) (Proxy :: Proxy cs') :: ( Known Length cs''
                                                              , All Functor cs''
                                                              , All Functor cs') :- All Functor (cs'' ++ cs')) \\
  (iwithoutRetainsAll (Proxy :: Proxy Functor) :: ( IWithout n cs cs''
                                                  , All Functor cs) :- All Functor cs'')

forsOn_ ::
     forall m n cs cs' cs'' r c.
     ( Functor m
     , All Functor cs
     , IWithout n cs cs''
     , All Functor (cs'' ++ cs')
     , All Functor cs'
     , Known Length cs''
     )
  => IIndex n cs c
  -> Node cs m r
  -> (forall x. c x -> Node cs' m x)
  -> Node (cs'' ++ cs') m r
forsOn_ n node f = transform alg node
  where
    alg (ReturnF r) = ReturnF r
    alg (EffectF eff) = EffectF eff
    alg (ConnectF con) =
      case fdecompIdx n con of
        Left other -> ConnectF (finl proxyInner other)
        Right c -> getNode $ join $ mapsAll (finr proxyOuter) $ f c
    proxyInner :: Proxy cs'
    proxyInner = Proxy
    proxyOuter :: Proxy cs''
    proxyOuter = Proxy

-- | Loop over a 'Node', replacing each 'yieldOn' the specified
-- channel with a computation with a different list of channels.
--
-- This is merely a specialisation of 'forsOn' for 'Yielding'.
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
     , IWithout n cs cs''
     , All Functor cs'
     , Known Length cs''
     )
  => IIndex n cs (Yielding a) -- ^ A channel over which to loop.
  -> Node cs m r -- ^ A source of values to loop over.
  -> (a -> Node cs' m ()) -- ^ Loop body.
  -> Node (cs'' ++ cs') m r
forOn n node f = forsOn n node (\(a, r) -> r <$ f a)

-- | Loop over a 'Node', replacing each 'awaitOn' the specified
-- channel by the loop body, which should provide the value asked for.
--
-- This is merely a specialisation of 'forsOn' for 'Awaiting'.
--
-- ====__Signatures for some specific indices__
-- @
-- 'preforOn' 'i0' ::
--       ( 'Functor' 'm', 'All' 'Functor' cs, 'All' 'Functor' cs'
--       , 'Known' 'Length' cs)
--    => 'Node' ('Awaiting' a : cs) m r
--    -> 'Node' cs' m a
--    -> 'Node' (cs 'Type.Family.List.++' cs') m r
--
-- 'preforOn' 'i1' ::
--       ( 'Functor' 'm', 'Functor' c0
--       , 'All' 'Functor' cs, 'All' 'Functor' cs'
--       , 'Known' 'Length' cs)
--    => 'Node' (c0 : 'Awaiting' a : cs) m r
--    -> 'Node' cs' m a
--    -> 'Node' ((c0 : cs) 'Type.Family.List.++' cs') m r
--
-- 'preforOn' 'i2' ::
--       ( 'Functor' 'm', 'Functor' c0, 'Functor' c1
--       , 'All' 'Functor' cs, 'All' 'Functor' cs'
--       , 'Known' 'Length' cs)
--    => 'Node' (c0 : c1 : 'Awaiting' a : cs) m r
--    -> 'Node' cs' m a
--    -> 'Node' ((c0 : c1 : cs) 'Type.Family.List.++' cs') m r
-- @
preforOn ::
     ( Known Length cs''
     , IWithout n cs cs''
     , Functor m
     , All Functor cs'
     , All Functor cs
     )
  => IIndex n cs (Awaiting a) -- ^ A channel over which to loop.
  -> Node cs m r -- ^ A receiver of values.
  -> Node cs' m a -- ^ A provider of values, run once for each
                  -- 'awaitOn'.
  -> Node (cs'' ++ cs') m r
preforOn n node body = forsOn n node (<$> body)

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
