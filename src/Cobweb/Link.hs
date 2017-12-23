{-|
Module: Cobweb.Link
Description: Linking nodes in a graph.
Copyright: 2017 © Ivan Timokhin
License: BSD3
Maintainer: timokhin.iv@gmail.com
Stability: experimental

This module contains functions and operators that deal with
communication between nodes on compatible channels.

__Note on termination:__ in all of the functions in this module, the
first node to terminate brings down the entire resulting computation.
-}
{-# OPTIONS_HADDOCK show-extensions #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE UndecidableInstances #-}

module Cobweb.Link
  (
    -- * Simplex communication
    -- $simplex
    (>->)
  , (|->)
  , (>-|)
  , linkOn
  , linkOn'
    -- * Duplex communication
    -- $duplex
  , (+>>)
  , (>+>)
  , (>>~)
  , (>~>)
  , (|>~)
  , (+>|)
  , linkOnDuplex
  , linkOnDuplex'
    -- * Generic linking
  , genericLinkOn
  ) where

import Data.Functor.Compose (Compose(getCompose))
import Data.Functor.Identity (Identity(Identity))
import Data.Proxy (Proxy(Proxy))
import Type.Class.Witness (Witness((\\)))
import Type.Family.List (Last, Null)
import Type.Family.Nat (Len, Pred)

import Cobweb.Core (Await, Request, Yield)
import Cobweb.Internal (Node, unconsNode, build)
import Cobweb.Type.Combinators
  ( Append
  , FSum
  , IIndex
  , Remove
  , RemoveW
  , fdecompIdx
  , finl
  , finr
  , i0
  , lastIndex
  , removeW
  )
import Cobweb.Type.Lemmata (removeNonEmpty)

-- $simplex
--
-- ‘Simplex’ here refers to the way values are passed through the
-- connection—in one direction, from one node to another.  This in
-- contrast with duplex communication, where both nodes provide and
-- receive values from each another.
--
-- That said, it is certainly possible to arrange bidirectional
-- transfer with functions from this section (e.g. using 'Annihilate'
-- instance for 'Compose'), but this sort of quasi-duplex
-- communication will have different semantics from the one provided
-- by dedicated duplex linking functions; the latter is designed to
-- closer match the concept of coroutines.
--
-- ====__Note on control flow__
--
-- Since the types of the functions in this section do not enforce any
-- particular control flow (execution can start from either 'Node'),
-- it has to be established by convention.  The convention (which
-- typically matches expected behaviour) is that the execution is
-- driven by the /second/ 'Node'; for typical
-- 'Cobweb.Core.Producer'—'Cobweb.Core.Pipe'—'Cobweb.Core.Consumer'
-- this corresponds to pull-based execution.

-- FIXME Haddock generates bad links for Producer/Consumer: 'v:'
-- (presumably, for values) instead of 't:'

-- | Connect two pipe-like nodes.
--
-- ====__Example types__
--
-- This operator can be thought of as having the following types:
--
-- @
-- ('>->') ::
--      'Functor' m
--   => 'Cobweb.Core.Producer' a m r
--   -> 'Cobweb.Core.Consumer' a m r
--   -> 'Cobweb.Core.Effect' m r
--
-- ('>->') ::
--      'Functor' m
--   => 'Cobweb.Core.Producer' a m r
--   -> 'Cobweb.Core.Pipe' a b m r
--   -> 'Cobweb.Core.Producer' b m r
--
-- ('>->') ::
--      'Functor' m
--   => 'Cobweb.Core.Pipe' a b m r
--   -> 'Cobweb.Core.Consumer' b m r
--   -> 'Cobweb.Core.Consumer' a m r
--
-- ('>->') ::
--      'Functor' m
--   => 'Cobweb.Core.Pipe' a b m r
--   -> 'Cobweb.Core.Pipe' b c m r
--   -> 'Cobweb.Core.Pipe' a c m r
-- @
--
-- as well as some more exotic types like this:
--
-- @
-- ('>->') ::
--      ( 'Functor' m
--      , 'Functor' l0
--      , 'Functor' l1
--      , 'Functor' r1
--      , 'Functor' r2
--      , 'Annihilate' r0 l2
--      )
--   => 'Node' '[l0, l1, l2] m r
--   -> 'Node' '[r0, r1, r2] m r
--   -> 'Node' '[l0, l1, r1, r2] m r
-- @
--
-- However, the primary intended use of this operator is closer to the
-- first group of types, and this generality should not be abused.
(>->) ::
     forall lcs lcs' b rcs' rescs m a.
     ( Remove (Pred (Len lcs)) lcs lcs'
     , Last lcs ~ Yield b
     , Append lcs' rcs' rescs
     )
  => Node lcs m a -- ^ ‘Upstream’ node.
  -> Node (Await b : rcs') m a -- ^ ‘Downstream’ node.
  -> Node rescs m a
{-# INLINE (>->) #-}
(>->) = linkPipe_ \\ removeNonEmpty lrem
  where
    lrem :: RemoveW (Pred (Len lcs)) lcs lcs'
    lrem = removeW

infixl 8 >->

linkPipe_ ::
     ( Remove (Pred (Len lcs)) lcs lcs'
     , Null lcs ~ 'False
     , Last lcs ~ Yield b
     , Append lcs' rcs' rescs
     )
  => Node lcs m a
  -> Node (Await b : rcs') m a
  -> Node rescs m a
{-# INLINE linkPipe_ #-}
linkPipe_ = linkOn lastIndex i0

-- | A depth-first traversal of a communication tree, starting from a
-- producer.
--
-- This operator ‘attaches’ a 'Node' to the first channel of the
-- ‘producer’, putting its other channels up front.  This way,
-- subsequent invocations of @('|->')@ will bind to those channels (if
-- there are any), thus generating a depth-first traversal from the
-- root on the left side.
--
-- ====__Example__
--
-- @
-- 'Cobweb.Core.run' '$' 'Cobweb.Producer.each' [1..3] '>->' 'Cobweb.Unzip.tee' '|->' 'Cobweb.Pipe.mapping' (* 2) '>->' 'Cobweb.Unzip.tee' '|->' 'Cobweb.Pipe.mapping' (+ 50) '>->' 'Cobweb.Consumer.drain' ('Text.Printf.printf' "0: %d\\n")
--                                                     '|->' 'Cobweb.Consumer.drain' ('Text.Printf.printf' "1: %d\\n")
--                           '|->' 'Cobweb.Pipe.mapping' (* 10) '>->' 'Cobweb.Consumer.drain' ('Text.Printf.printf' "2: %d\\n")
-- @
--
-- prints
--
-- @
-- 0: 52
-- 1: 2
-- 2: 10
-- 0: 54
-- 1: 4
-- 2: 20
-- 0: 56
-- 1: 6
-- 2: 30
-- @
--
-- While the indentation in the example certainly helps to understand
-- the data flow, it is, unfortunately, not enforced in any way.
(|->) ::
     Append rcs lcs rescs
  => Node (Yield b : lcs) m a -- ^ ‘Producer’.
  -> Node (Await b : rcs) m a -- ^ Attached node.
  -> Node rescs m a
{-# INLINE (|->) #-}
(|->) = linkOn' i0 i0

infixl 7 |->

-- | A depth-first traversal of a connection tree, starting from a
-- consumer.
--
-- This operator ‘attaches’ a /right/ 'Node' to the last channel of
-- the /left/ ‘consumer’, putting attached @'Node'@'s channels in the
-- back.  This way, subsequent (/previous/ syntactically, because of
-- fixity) invocations of @('>-|')@ bind to those channels, thus
-- generating a depth-first traversal from the root on the right side.
--
-- ====__Example__
--
-- (best read right-to-left)
--
-- @
-- 'Cobweb.Core.run' '$'                   'Cobweb.Producer.each' [1..3] '>->' 'Cobweb.Pipe.mapping' 'show' '>-|'
--       'Cobweb.Producer.each' ["a", "b", "c"] '>->' 'Cobweb.Pipe.mapping' ('map' 'Data.Char.toUpper') '>-|' 'Cobweb.Zip.zippingWith' ('Data.List.++') '>-|'
--                            'Cobweb.Producer.each' [\"X\", \"Y\", \"Z\"] '>->' 'Cobweb.Pipe.mapping' ('map' 'Data.Char.toLower') '>-|' 'Cobweb.Zip.zippingWith' ('Data.List.++') '>->' 'Cobweb.Consumer.drain' 'print'
-- @
--
-- prints
--
-- @
-- "1Ax"
-- "2By"
-- "3Cz"
-- @
(>-|) ::
     forall lcs rcs lcs' rcs' rescs m b a.
     ( Remove (Pred (Len lcs)) lcs lcs'
     , Remove (Pred (Len rcs)) rcs rcs'
     , Last rcs ~ Await b
     , Last lcs ~ Yield b
     , Append rcs' lcs' rescs
     )
  => Node lcs m a -- ^ Attached node.
  -> Node rcs m a -- ^ ‘Consumer’.
  -> Node rescs m a
{-# INLINE (>-|) #-}
(>-|) = linkConsumer_ \\ removeNonEmpty lrem \\ removeNonEmpty rrem
  where
    lrem :: RemoveW (Pred (Len lcs)) lcs lcs'
    lrem = removeW
    rrem :: RemoveW (Pred (Len rcs)) rcs rcs'
    rrem = removeW

infixr 7 >-|

linkConsumer_ ::
     ( Null lcs ~ 'False
     , Null rcs ~ 'False
     , Remove (Pred (Len lcs)) lcs lcs'
     , Remove (Pred (Len rcs)) rcs rcs'
     , Last rcs ~ Await b
     , Last lcs ~ Yield b
     , Append rcs' lcs' rescs
     )
  => Node lcs m a
  -> Node rcs m a
  -> Node rescs m a
{-# INLINE linkConsumer_ #-}
linkConsumer_ = linkOn' lastIndex lastIndex

-- | Link nodes on a specified pair of channels, putting first node's
-- channels first in the result.
--
-- Modulo some magic to cut down on redundant constraints,
--
-- @
-- ('>->') = 'linkOn' 'lastIndex' 'i0'
-- @
linkOn ::
     forall n k lcs lcs' rcs rcs' rescs m b r.
     ( Remove n lcs lcs'
     , Remove k rcs rcs'
     , Append lcs' rcs' rescs
     )
  => IIndex n lcs (Yield b) -- ^ The index of the linked channel on the first node.
  -> IIndex k rcs (Await b) -- ^ The index of the linked channel on the
     -- second node.
  -> Node lcs m r
  -> Node rcs m r
  -> Node rescs m r
{-# INLINE linkOn #-}
linkOn n k =
  genericLinkOn
    annihilateIdentity
    annihilateYield
    (fmap Identity)
    Identity
    (finl proxyR)
    (finr proxyL)
    n
    k .
  Identity
  where
    proxyR = Proxy :: Proxy rcs'
    proxyL = Proxy :: Proxy lcs'

-- | Link nodes on a specified pair of channels, putting second node's
-- channels first in the result.
--
-- Modulo some magic to cut down on redundant constraints,
--
-- @
-- ('|->') = 'linkOn'' 'i0' 'i0'
-- ('>-|') = 'linkOn'' 'lastIndex' 'lastIndex'
-- @
linkOn' ::
     forall n k lcs lcs' rcs rcs' rescs b m r.
     ( Remove n lcs lcs'
     , Remove k rcs rcs'
     , Append rcs' lcs' rescs
     )
  => IIndex n lcs (Yield b) -- ^ The index of the linked channel on the first node.
  -> IIndex k rcs (Await b) -- ^ The index of the linked channel on the
     -- second node.
  -> Node lcs m r
  -> Node rcs m r
  -> Node rescs m r
{-# INLINE linkOn' #-}
linkOn' n k =
  genericLinkOn
    annihilateIdentity
    annihilateYield
    (fmap Identity)
    Identity
    (finr proxyR)
    (finl proxyL)
    n
    k .
  Identity
  where
    proxyR = Proxy :: Proxy rcs'
    proxyL = Proxy :: Proxy lcs'

-- $duplex
--
-- See "Cobweb.Duplex" for brief explanation of how duplex
-- communication works, and example 'Node's.
--
-- Since at every moment, only one 'Node' in the graph is not blocked
-- awaiting response, the control flow in duplex communication is
-- completely unambiguous, unlike convention-based control flow of
-- simplex links; that is, immediately available 'Node' (as in, the
-- one not wrapped in the communication functor) is always run first.

-- | Pull-based linking of two 'Node's.
--
-- ====__Example types__
--
-- This operator can be thought of as having the following types:
--
-- @
-- ('+>>') ::
--      'Functor' m
--   => (b -> 'Cobweb.Duplex.Client' a b m r)
--   -> 'Cobweb.Duplex.Client' b a m r
--   -> 'Cobweb.Core.Effect' m r
--
-- ('+>>') ::
--      'Functor' m
--   => (a' -> 'Cobweb.Duplex.Client' a a' m r)
--   -> 'Cobweb.Duplex.Proxy' a' a b' b m r
--   -> 'Cobweb.Duplex.Client' b b' m r
--
-- ('+>>') ::
--      'Functor' m
--   => (b' -> 'Cobweb.Duplex.Proxy' a' a b' b m r)
--   -> 'Cobweb.Duplex.Client' b' b m r
--   -> 'Cobweb.Duplex.Client' a' a m r
--
-- ('+>>') ::
--      'Functor' m
--   => (b' -> 'Cobweb.Duplex.Proxy' a' a b' b m r)
--   -> 'Cobweb.Duplex.Proxy' b' b c' c m r
--   -> 'Cobweb.Duplex.Proxy' a' a c' c m r
-- @
(+>>) ::
     forall lcs lcs' rcs' rescs m b c a.
     ( Remove (Pred (Len lcs)) lcs lcs'
     , Last lcs ~ Request b c
     , Append lcs' rcs' rescs
     )
  => (c -> Node lcs m a) -- ^ Upstream ‘server’ node.
  -> Node (Request c b : rcs') m a -- ^ Downstream ‘client’
                                          -- node.
  -> Node rescs m a
{-# INLINE (+>>) #-}
(+>>) = linkDuplexPullPipe_ \\ removeNonEmpty lrem
  where
    lrem :: RemoveW (Pred (Len lcs)) lcs lcs'
    lrem = removeW

infixr 5 +>>

-- | A point-free version of @('+>>')@.
--
-- ====__Example types__
--
-- This operator can be thought of as having the following types:
--
-- @
-- ('>+>') ::
--      'Functor' m
--   => (a' -> 'Cobweb.Duplex.Client' a a' m r)
--   -> (b' -> 'Cobweb.Duplex.Proxy' a' a b' b m r)
--   -> (b' -> 'Cobweb.Duplex.Client' b b' m r)
--
-- ('>+>') ::
--      'Functor' m
--   => (b' -> 'Cobweb.Duplex.Proxy' a' a b' b m r)
--   -> (c' -> 'Cobweb.Duplex.Proxy' b' b c' c m r)
--   -> (c' -> 'Cobweb.Duplex.Proxy' a' a c' c m r)
-- @
(>+>) ::
     ( Remove (Pred (Len lcs)) lcs lcs'
     , Last lcs ~ Request b c
     , Append lcs' rcs' rescs
     )
  => (c -> Node lcs m a) -- ^ Upstream ‘server’ node.
  -> (d -> Node (Request c b : rcs') m a) -- ^ Downstream
     -- ‘client’ node.
  -> (d -> Node rescs m a)
{-# INLINE (>+>) #-}
(>+>) left = fmap (left +>>)

infixl 6 >+>

linkDuplexPullPipe_ ::
     ( Remove (Pred (Len lcs)) lcs lcs'
     , Null lcs ~ 'False
     , Last lcs ~ Request b c
     , Append lcs' rcs' rescs
     )
  => (c -> Node lcs m r)
  -> Node (Request c b : rcs') m r
  -> Node rescs m r
{-# INLINE linkDuplexPullPipe_ #-}
linkDuplexPullPipe_ = linkOnDuplex lastIndex i0

-- | Push-based linking of two 'Node's.
--
-- ====__Example types__
--
-- This operator can be thought of as having the following types:
--
-- @
-- ('>>~') ::
--      'Functor' m
--   => 'Cobweb.Duplex.Client' a a' m r
--   -> (a -> 'Cobweb.Duplex.Client' a' a m r)
--   -> 'Cobweb.Core.Effect' m r
--
-- ('>>~') ::
--      'Functor' m
--   => 'Cobweb.Duplex.Client' a a' m r
--   -> (a -> 'Cobweb.Duplex.Proxy' a' a b' b m r)
--   -> 'Cobweb.Duplex.Client' b b' m r
--
-- ('>>~') ::
--      'Functor' m
--   => 'Cobweb.Duplex.Proxy' a' a b' b m r
--   -> (b -> 'Cobweb.Duplex.Client' b' b m r)
--   -> 'Cobweb.Duplex.Client' a' a m r
--
-- ('>>~') ::
--      'Functor' m
--   => 'Cobweb.Duplex.Proxy' a' a b' b m r
--   -> (b -> 'Cobweb.Duplex.Proxy' b' b c' c m r)
--   -> 'Cobweb.Duplex.Proxy' a' a c' c m r
-- @
(>>~) ::
     forall lcs lcs' rcs' rescs m b c a.
     ( Remove (Pred (Len lcs)) lcs lcs'
     , Last lcs ~ Request b c
     , Append lcs' rcs' rescs
     )
  => Node lcs m a -- ^ Upstream ‘client’ node.
  -> (b -> Node (Request c b : rcs') m a) -- ^ Downstream ‘server’
     -- node.
  -> Node rescs m a
{-# INLINE (>>~) #-}
(>>~) = linkDuplexPushPipe_ \\ removeNonEmpty lrem
  where
    lrem :: RemoveW (Pred (Len lcs)) lcs lcs'
    lrem = removeW

infixl 5 >>~

-- | A point-free version of @('>>~')@.
--
-- ====__Example types__
--
-- This operator can be thought of as having the following types:
--
-- @
-- ('>~>') ::
--      'Functor' m
--   => (a -> 'Cobweb.Duplex.Proxy' a' a b' b m r)
--   -> (b -> 'Cobweb.Duplex.Client' b' b m r)
--   -> (a -> 'Cobweb.Duplex.Client' a' a m r)
--
-- ('>~>') ::
--      'Functor' m
--   => (a -> 'Cobweb.Duplex.Proxy' a' a b' b m r)
--   -> (b -> 'Cobweb.Duplex.Proxy' b' b c' c m r)
--   -> (a -> 'Cobweb.Duplex.Proxy' a' a c' c m r)
-- @
(>~>) ::
     ( Remove (Pred (Len lcs)) lcs lcs'
     , Last lcs ~ Request b c
     , Append lcs' rcs' rescs
     )
  => (d -> Node lcs m a) -- ^ Upstream ‘client’ node.
  -> (b -> Node (Request c b : rcs') m a) -- ^ Downstream
     -- ‘server’ node.
  -> (d -> Node rescs m a)
{-# INLINE (>~>) #-}
left >~> right = fmap (>>~ right) left

infixl 6 >~>

linkDuplexPushPipe_ ::
     ( Remove (Pred (Len lcs)) lcs lcs'
     , Null lcs ~ 'False
     , Last lcs ~ Request b c
     , Append lcs' rcs' rescs
     )
  => Node lcs m r
  -> (b -> Node (Request c b : rcs') m r)
  -> Node rescs m r
{-# INLINE linkDuplexPushPipe_ #-}
linkDuplexPushPipe_ = flip (linkOnDuplex' i0 lastIndex)

-- | @('|>~')@ is to @('>>~')@ what @('|->')@ is to @('>->')@.
(|>~) ::
     Append rcs lcs rescs
  => Node (Request b c : lcs) m r -- ^ A ‘client’ node.
  -> (b -> Node (Request c b : rcs) m r) -- ^ A ‘server’ node.
  -> Node rescs m r
{-# INLINE (|>~) #-}
(|>~) = flip (linkOnDuplex i0 i0)

infixl 4 |>~

-- | @('+>|')@ is to @('+>>')@ what @('>-|')@ is to @('>->')@.
(+>|) ::
     forall lcs lcs' rcs rcs' rescs b c m a.
     ( Remove (Pred (Len lcs)) lcs lcs'
     , Remove (Pred (Len rcs)) rcs rcs'
     , Last lcs ~ Request b c
     , Last rcs ~ Request c b
     , Append rcs' lcs' rescs
     )
  => (c -> Node lcs m a) -- ^ A ‘server’ node.
  -> Node rcs m a -- ^ A ‘client’ node.
  -> Node rescs m a
{-# INLINE (+>|) #-}
(+>|) = linkConsumerDuplex_ \\ removeNonEmpty lrem \\ removeNonEmpty rrem
  where
    lrem :: RemoveW (Pred (Len lcs)) lcs lcs'
    lrem = removeW
    rrem :: RemoveW (Pred (Len rcs)) rcs rcs'
    rrem = removeW

infixr 4 +>|

linkConsumerDuplex_ ::
     ( Remove (Pred (Len rcs)) rcs rcs'
     , Remove (Pred (Len lcs)) lcs lcs'
     , Null lcs ~ 'False
     , Null rcs ~ 'False
     , Last lcs ~ Request b c
     , Last rcs ~ Request c b
     , Append rcs' lcs' rescs
     )
  => (c -> Node lcs m a)
  -> Node rcs m a
  -> Node rescs m a
{-# INLINE linkConsumerDuplex_ #-}
linkConsumerDuplex_ = linkOnDuplex' lastIndex lastIndex

-- | Link nodes on a specified pair of duplex channels, putting first
-- (‘server’) node's channels first in the result.
linkOnDuplex ::
     forall n k lcs lcs' rcs rcs' b c rescs m r.
     (Remove n lcs lcs', Remove k rcs rcs', Append lcs' rcs' rescs)
  => IIndex n lcs (Request b c) -- ^ The index of the linked
     -- channel on the ‘server’ node.
  -> IIndex k rcs (Request c b) -- ^ The index of the linked
     -- channel on the ‘client’ node.
  -> (c -> Node lcs m r) -- ^ ‘Server’ node.
  -> Node rcs m r -- ^ ‘Client’ node.
  -> Node rescs m r
{-# INLINE linkOnDuplex #-}
linkOnDuplex =
  genericLinkOn
    annihilateYield
    annihilateYield
    getCompose
    getCompose
    (finl proxyR)
    (finr proxyL)
  where
    proxyR :: Proxy rcs'
    proxyR = Proxy
    proxyL :: Proxy lcs'
    proxyL = Proxy

-- | Link nodes on a specified pair of duplex channels, putting second
-- (‘client’) node's channels first in the result.
linkOnDuplex' ::
     forall n k lcs lcs' rcs rcs' rescs m b c r.
     (Remove k rcs rcs', Remove n lcs lcs', Append rcs' lcs' rescs)
  => IIndex n lcs (Request b c) -- ^ The index of the linked
     -- channel on the ‘server’ node.
  -> IIndex k rcs (Request c b) -- ^ The index of the linked
     -- channel on the ‘client’ node.
  -> (c -> Node lcs m r) -- ^ ‘Server’ node.
  -> Node rcs m r -- ^ ‘Client’ node.
  -> Node rescs m r
{-# INLINE linkOnDuplex' #-}
linkOnDuplex' =
  genericLinkOn
    annihilateYield
    annihilateYield
    getCompose
    getCompose
    (finr proxyR)
    (finl proxyL)
  where
    proxyR :: Proxy rcs'
    proxyR = Proxy
    proxyL :: Proxy lcs'
    proxyL = Proxy

-- | The most generic linking function, used to implement all other
-- function in this module.  Calling it directly is practically never
-- needed.
genericLinkOn ::
     (Functor rreq, Functor lreq, Remove n lcs lcs', Remove k rcs rcs')
  => (forall x y. lreq x -> rresp y -> (x, y))
  -> (forall x y. rreq x -> lresp y -> (x, y))
  -> (forall x. lc x -> lresp (lreq x)) -- ^ Convert the channel on
     -- the first node to a duplex representation.
  -> (forall x. rc x -> rresp (rreq x)) -- ^ Convert the channel on
     -- the second node to a duplex representation.
  -> (forall x. FSum lcs' x -> FSum rescs x) -- ^ Embed remaining
     -- channels of the first node into the resulting list.
  -> (forall x. FSum rcs' x -> FSum rescs x) -- ^ Embed remaining
     -- channels of the second node into the resulting list.
  -> IIndex n lcs lc -- ^ The index of the linked channel on the first
                     -- node.
  -> IIndex k rcs rc -- ^ The index of the linked channel on the
                     -- second node.
  -> lreq (Node lcs m a)
  -> Node rcs m a
  -> Node rescs m a
{-# INLINE genericLinkOn #-}
genericLinkOn lannihilate rannihilate ldecompose rdecompose lembed rembed n k =
  \l r ->
    build
      (\ret con lft ->
         let loop left =
               unconsNode
                 ret
                 (\cs cont ->
                    case fdecompIdx k cs of
                      Left other -> con (rembed other) (loop left . cont)
                      Right c ->
                        case lannihilate left (rdecompose c) of
                          (left', right') -> loop' (fmap cont right') left')
                 (\e cont -> lft e (loop left . cont))
             loop' right =
               unconsNode
                 ret
                 (\cs cont ->
                    case fdecompIdx n cs of
                      Left other -> con (lembed other) (loop' right . cont)
                      Right c ->
                        case rannihilate right (ldecompose c) of
                          (right', left') -> loop (fmap cont left') right')
                 (\e cont -> lft e (loop' right . cont))
         in loop l r)

annihilateYield :: (a -> x) -> Yield a y -> (x, y)
annihilateYield f (a, y) = (f a, y)

annihilateIdentity :: Identity x -> Identity y -> (x, y)
annihilateIdentity (Identity x) (Identity y) = (x, y)
