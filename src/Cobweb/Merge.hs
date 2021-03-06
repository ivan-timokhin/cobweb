{-|
Module: Cobweb.Merge
Description: Merging together identical channels of a Node.
Copyright: 2017 © Ivan Timokhin
License: BSD3
Maintainer: timokhin.iv@gmail.com
Stability: experimental

This module provides functions for identifying identical channels of a
'Node'; this can be useful, for example, if several 'Node's linked
together all need to communicate to the same ‘service’, which is
represented by another 'Node'.

Note that they provide limited support for loops in communication
graphs; e.g., it is possible to arrange the following communication
scheme, provided that one node in the loop is unable to distinguish
its two channels:

@
      +---+
  +---| b |---+
  |   +---+   |
+-+-+       +-+-+
| a |       | c |
+-+-+       +-+-+
  |   +---+   |
  +---| d |---+
      +---+
@

-}
{-# OPTIONS_HADDOCK show-extensions #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE TypeOperators #-}

module Cobweb.Merge
  ( merge
  , mergeWith
  , mergeWithMap
  , mergeAll
  ) where

import Data.Type.Equality (type (==))

import Cobweb.Core (Leaf, Yield, gmapAll, mapYield)
import Cobweb.Internal (Node)
import Cobweb.Type.Combinators
  ( AllEqual
  , FSum(FInL)
  , IIndex
  , Inductive
  , Remove
  , Replace
  , mergeSum
  , mergeSumAll
  , mergeSumWith
  )

-- | Given (different) indices of two identical channels of a 'Node',
-- merge them together at the location of the /second/ index, dropping
-- the first one.
--
-- ====__Signatures for some specific indices__
--
-- @
-- 'merge' 'Cobweb.Core.i0' 'Cobweb.Core.i1' ::
--      ('Functor' c, 'Functor' m, 'All' 'Functor' cs)
--   => 'Node' (c : c : cs) m r
--   -> 'Node' (c : cs) m r
--
-- 'merge' 'Cobweb.Core.i0' 'Cobweb.Core.i2' ::
--      ('Functor' c1, 'Functor' c, 'Functor' m, 'All' 'Functor' cs)
--   => 'Node' (c : c1 : c : cs) m r
--   -> 'Node' (c1 : c : cs) m r
--
-- 'merge' 'Cobweb.Core.i0' 'Cobweb.Core.i3' ::
--      ( 'Functor' c1
--      , 'Functor' c2
--      , 'Functor' c
--      , 'Functor' m
--      , 'All' 'Functor cs
--      )
--   => 'Node' (c : c1 : c2 : c : cs) m r
--   -> 'Node' (c1 : c2 : c : cs) m r
--
-- 'merge' 'Cobweb.Core.i1' 'Cobweb.Core.i0' ::
--      ('Functor' c, 'Functor' m, 'All' 'Functor' cs)
--   => 'Node' (c : c : cs) m r
--   -> 'Node' (c : cs) m r
--
-- 'merge' 'Cobweb.Core.i1' 'Cobweb.Core.i2' ::
--      ('Functor' c0, 'Functor' c, 'Functor' m, 'All' 'Functor' cs)
--   => 'Node' (c0 : c : c : cs) m r
--   -> 'Node' (c0 : c : cs) m r
--
-- 'merge' 'Cobweb.Core.i1' 'Cobweb.Core.i3' ::
--      ( 'Functor' c0
--      , 'Functor' c2
--      , 'Functor' c
--      , 'Functor' m
--      , 'All' 'Functor' cs
--      )
--   => 'Node' (c0 : c : c2 : c : cs) m r
--   -> 'Node' (c0 : c2 : c : cs) m r
--
-- 'merge' 'Cobweb.Core.i2' 'Cobweb.Core.i0' ::
--      ('Functor' c1, 'Functor' c, 'Functor' m, 'All' 'Functor' cs)
--   => 'Node' (c : c1 : c : cs) m r
--   -> 'Node' (c : c1 : cs) m r
--
-- 'merge' 'Cobweb.Core.i2' 'Cobweb.Core.i1' ::
--      ('Functor' c0, 'Functor' c, 'Functor' m, 'All' 'Functor' cs)
--   => 'Node' (c0 : c : c : cs) m r
--   -> 'Node' (c0 : c : cs) m r
--
-- 'merge' 'Cobweb.Core.i2' 'Cobweb.Core.i3' ::
--      ( 'Functor' c0
--      , 'Functor' c1
--      , 'Functor' c
--      , 'Functor' m
--      , 'All' 'Functor' cs
--      )
--   => 'Node' (c0 : c1 : c : c : cs) m r
--   -> 'Node' (c0 : c1 : c : cs) m r
-- @
merge ::
     ((n == k) ~ 'False, Remove n cs cs')
  => IIndex n cs c -- ^ Index of the first merged channel (this one is
                   -- removed).
  -> IIndex k cs c -- ^ Index of the second merged channel (this one is
                   -- kept).
  -> Node cs m r
  -> Node cs' m r
merge n k = gmapAll (mergeSum n k)

-- | Given a way to transform two different channels of a 'Node' into
-- a common form, merge them together at the location of the second
-- index.
--
-- Conceptually,
--
-- @
-- 'merge' = 'mergeWith' 'id' 'id'
-- @
mergeWith ::
     ((n == k) ~ 'False, Replace k cs c' cs', Remove n cs' cs'')
  => (forall x. c1 x -> c' x) -- ^ Transform the first channel into a
                              -- common one.
  -> (forall x. c2 x -> c' x) -- ^ Transform the second channel into a
                              -- common one.
  -> IIndex n cs c1 -- ^ Index of the first merged channel (this one is
                    -- removed).
  -> IIndex k cs c2 -- ^ Index of the second merged channel (this one
                    -- is replaced).
  -> Node cs m r
  -> Node cs'' m r
mergeWith f g n k = gmapAll (mergeSumWith f g n k)

-- | A specialisation of 'mergeWith' for 'Yield' channels.
mergeWithMap ::
     ((n == k) ~ 'False, Replace k cs (Yield c) cs', Remove n cs' cs'')
  => (a -> c) -- ^ Transform the values on the first channel.
  -> (b -> c) -- ^ Transform the values on the second channel.
  -> IIndex n cs (Yield a) -- ^ Index of the removed channel.
  -> IIndex k cs (Yield b) -- ^ Index of the replaced channel.
  -> Node cs m r
  -> Node cs'' m r
mergeWithMap f g = mergeWith (mapYield f) (mapYield g)

-- | Given a 'Node' with /all/ channels identical, merge them all
-- together.
mergeAll :: (cs `AllEqual` c, Inductive cs) => Node cs m r -> Leaf c m r
mergeAll = gmapAll (FInL . mergeSumAll)
