{-|
Module: Cobweb.Fuse
Description: Fusing together identical channels of a Node.
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

module Cobweb.Fuse
  ( fuse
  , fuseWith
  , fuseWithMap
  , fuseAll
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
  , fuseSum
  , fuseSumAll
  , fuseSumWith
  )

-- | Given (different) indices of two identical channels of a 'Node',
-- fuse them together at the location of the /second/ index, dropping
-- the first one.
--
-- ====__Signatures for some specific indices__
--
-- @
-- 'fuse' 'Cobweb.Core.i0' 'Cobweb.Core.i1' ::
--      ('Functor' c, 'Functor' m, 'All' 'Functor' cs)
--   => 'Node' (c : c : cs) m r
--   -> 'Node' (c : cs) m r
--
-- 'fuse' 'Cobweb.Core.i0' 'Cobweb.Core.i2' ::
--      ('Functor' c1, 'Functor' c, 'Functor' m, 'All' 'Functor' cs)
--   => 'Node' (c : c1 : c : cs) m r
--   -> 'Node' (c1 : c : cs) m r
--
-- 'fuse' 'Cobweb.Core.i0' 'Cobweb.Core.i3' ::
--      ( 'Functor' c1
--      , 'Functor' c2
--      , 'Functor' c
--      , 'Functor' m
--      , 'All' 'Functor cs
--      )
--   => 'Node' (c : c1 : c2 : c : cs) m r
--   -> 'Node' (c1 : c2 : c : cs) m r
--
-- 'fuse' 'Cobweb.Core.i1' 'Cobweb.Core.i0' ::
--      ('Functor' c, 'Functor' m, 'All' 'Functor' cs)
--   => 'Node' (c : c : cs) m r
--   -> 'Node' (c : cs) m r
--
-- 'fuse' 'Cobweb.Core.i1' 'Cobweb.Core.i2' ::
--      ('Functor' c0, 'Functor' c, 'Functor' m, 'All' 'Functor' cs)
--   => 'Node' (c0 : c : c : cs) m r
--   -> 'Node' (c0 : c : cs) m r
--
-- 'fuse' 'Cobweb.Core.i1' 'Cobweb.Core.i3' ::
--      ( 'Functor' c0
--      , 'Functor' c2
--      , 'Functor' c
--      , 'Functor' m
--      , 'All' 'Functor' cs
--      )
--   => 'Node' (c0 : c : c2 : c : cs) m r
--   -> 'Node' (c0 : c2 : c : cs) m r
--
-- 'fuse' 'Cobweb.Core.i2' 'Cobweb.Core.i0' ::
--      ('Functor' c1, 'Functor' c, 'Functor' m, 'All' 'Functor' cs)
--   => 'Node' (c : c1 : c : cs) m r
--   -> 'Node' (c : c1 : cs) m r
--
-- 'fuse' 'Cobweb.Core.i2' 'Cobweb.Core.i1' ::
--      ('Functor' c0, 'Functor' c, 'Functor' m, 'All' 'Functor' cs)
--   => 'Node' (c0 : c : c : cs) m r
--   -> 'Node' (c0 : c : cs) m r
--
-- 'fuse' 'Cobweb.Core.i2' 'Cobweb.Core.i3' ::
--      ( 'Functor' c0
--      , 'Functor' c1
--      , 'Functor' c
--      , 'Functor' m
--      , 'All' 'Functor' cs
--      )
--   => 'Node' (c0 : c1 : c : c : cs) m r
--   -> 'Node' (c0 : c1 : c : cs) m r
-- @
fuse ::
     ((n == k) ~ 'False, Remove n cs cs')
  => IIndex n cs c -- ^ Index of the first fused channel (this one is
                   -- removed).
  -> IIndex k cs c -- ^ Index of the second fused channel (this one is
                   -- kept).
  -> Node cs m r
  -> Node cs' m r
fuse n k = gmapAll (fuseSum n k)

-- | Given a way to transform two different channels of a 'Node' into
-- a common form, fuse them together at the location of the second
-- index.
--
-- Conceptually,
--
-- @
-- 'fuse' = 'fuseWith' 'id' 'id'
-- @
fuseWith ::
     ((n == k) ~ 'False, Replace k cs c' cs', Remove n cs' cs'')
  => (forall x. c1 x -> c' x) -- ^ Transform the first channel into a
                              -- common one.
  -> (forall x. c2 x -> c' x) -- ^ Transform the second channel into a
                              -- common one.
  -> IIndex n cs c1 -- ^ Index of the first fused channel (this one is
                    -- removed).
  -> IIndex k cs c2 -- ^ Index of the second fused channel (this one
                    -- is replaced).
  -> Node cs m r
  -> Node cs'' m r
fuseWith f g n k = gmapAll (fuseSumWith f g n k)

-- | A specialisation of 'fuseWith' for 'Yield' channels.
fuseWithMap ::
     ((n == k) ~ 'False, Replace k cs (Yield c) cs', Remove n cs' cs'')
  => (a -> c) -- ^ Transform the values on the first channel.
  -> (b -> c) -- ^ Transform the values on the second channel.
  -> IIndex n cs (Yield a) -- ^ Index of the removed channel.
  -> IIndex k cs (Yield b) -- ^ Index of the replaced channel.
  -> Node cs m r
  -> Node cs'' m r
fuseWithMap f g = fuseWith (mapYield f) (mapYield g)

-- | Given a 'Node' with /all/ channels identical, fuse them all
-- together.
fuseAll :: (cs `AllEqual` c, Inductive cs) => Node cs m r -> Leaf c m r
fuseAll = gmapAll (FInL . fuseSumAll)
