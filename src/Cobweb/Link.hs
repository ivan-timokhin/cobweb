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
{-# LANGUAGE FunctionalDependencies #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE UndecidableInstances #-}

module Cobweb.Link
  ( Annihilate(annihilate)
    -- * Simplex communication
    -- $simplex
  , (>->)
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
import Data.Functor.Identity (Identity(Identity, runIdentity))
import Data.Proxy (Proxy(Proxy))
import Data.Type.Length (Length)
import Data.Type.Sum.Lifted (FSum)
import Type.Class.Known (Known)
import Type.Class.Witness (Witness((\\)))
import Type.Family.List (type (++), Last, Null)
import Type.Family.Nat (Len, Pred)
import Data.Functor.Sum (Sum(InL, InR))
import Data.Functor.Product (Product(Pair))

import Cobweb.Internal
       (Node(Node, getNode), NodeF(ConnectF, EffectF, ReturnF))
import Cobweb.Type.Combinators
       (Remove, All, IIndex, fdecompIdx, finl, finr, i0, lastIndex)
import Cobweb.Type.Lemmata (iwithoutRetainsLength)

-- The functional dependency on Annihilate is very annoying, but in
-- its absence GHC can't even figure out that @Awaiting a@ and
-- @Yielding b@ pair only if @a ~ b@.  Unfortunately, this
-- significantly complicates adding named channels.
--
-- An alternative would be to explicitly demand that the functors are
-- additionally parametrised by the communicating type, and demand
-- that *that* matches without any additional dependencies on the
-- (bi|pro)functors themselves, but that would significantly
-- complicate custom channels.  Hrm.

-- | A definition of what it means for two functors to ‘match’ so that
-- they can be linked.
--
-- The essential idea here is that each functor carries with it
-- whatever is needed to extract the value from the other; the
-- instance for @(,)@ and @(->)@ is probably the clearest
-- demonstration of the concept (and also the most often used one).
class (Functor f, Functor g) =>
      Annihilate f g
  | f -> g
  , g -> f
  where
  -- | ‘Annihilate’ functor contexts, getting underlying values.
  annihilate :: f a -> g b -> (a, b)

instance Annihilate ((,) e) ((->) e) where
  annihilate (e, a) fb = (a, fb e)

instance Annihilate ((->) e) ((,) e) where
  annihilate fa (e, b) = (fa e, b)

instance Annihilate Identity Identity where
  annihilate x y = (runIdentity x, runIdentity y)

instance (Annihilate f1 g1, Annihilate f2 g2) =>
         Annihilate (Compose f1 f2) (Compose g1 g2) where
  annihilate x y = uncurry annihilate (annihilate (getCompose x) (getCompose y))

instance (Annihilate f1 g1, Annihilate f2 g2) =>
         Annihilate (Sum f1 f2) (Product g1 g2) where
  annihilate (InL f) (Pair g _) = annihilate f g
  annihilate (InR f) (Pair _ g) = annihilate f g

instance (Annihilate f1 g1, Annihilate f2 g2) =>
         Annihilate (Product f1 f2) (Sum g1 g2) where
  annihilate (Pair f _) (InL g) = annihilate f g
  annihilate (Pair _ f) (InR g) = annihilate f g

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
     forall lcs r rcs' m a.
     ( Null lcs ~ 'False
     , Known Length lcs
     , All Functor (Remove (Pred (Len lcs)) lcs)
     , All Functor rcs'
     , Annihilate r (Last lcs)
     , Functor m
     )
  => Node lcs m a -- ^ ‘Upstream’ node.
  -> Node (r : rcs') m a -- ^ ‘Downstream’ node.
  -> Node (Remove (Pred (Len lcs)) lcs ++ rcs') m a
(>->) = linkPipe_ \\ iwithoutRetainsLength idx
  where
    idx :: IIndex (Pred (Len lcs)) lcs (Last lcs)
    idx = lastIndex

infixl 8 >->

linkPipe_ ::
     ( Known Length lcs
     , Known Length (Remove (Pred (Len lcs)) lcs)
     , Null lcs ~ 'False
     , All Functor (Remove (Pred (Len lcs)) lcs)
     , All Functor rcs'
     , Annihilate r (Last lcs)
     , Functor m
     )
  => Node lcs m a
  -> Node (r : rcs') m a
  -> Node (Remove (Pred (Len lcs)) lcs ++ rcs') m a
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
     ( All Functor lcs
     , All Functor rcs
     , Known Length rcs
     , Annihilate r l
     , Functor m
     )
  => Node (l : lcs) m a -- ^ ‘Producer’.
  -> Node (r : rcs) m a -- ^ Attached node.
  -> Node (rcs ++ lcs) m a
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
     forall lcs rcs m a.
     ( Null lcs ~ 'False
     , Null rcs ~ 'False
     , Known Length lcs
     , Known Length rcs
     , All Functor (Remove (Pred (Len lcs)) lcs)
     , All Functor (Remove (Pred (Len rcs)) rcs)
     , Annihilate (Last rcs) (Last lcs)
     , Functor m
     )
  => Node lcs m a -- ^ Attached node.
  -> Node rcs m a -- ^ ‘Consumer’.
  -> Node (Remove (Pred (Len rcs)) rcs ++ Remove (Pred (Len lcs)) lcs) m a
(>-|) =
  linkConsumer_ \\ iwithoutRetainsLength lidx \\ iwithoutRetainsLength ridx
  where
    lidx :: IIndex (Pred (Len lcs)) lcs (Last lcs)
    lidx = lastIndex
    ridx :: IIndex (Pred (Len rcs)) rcs (Last rcs)
    ridx = lastIndex

infixr 7 >-|

linkConsumer_ ::
     ( Null lcs ~ 'False
     , Null rcs ~ 'False
     , Known Length (Remove (Pred (Len lcs)) lcs)
     , Known Length (Remove (Pred (Len rcs)) rcs)
     , Known Length lcs
     , Known Length rcs
     , Annihilate (Last rcs) (Last lcs)
     , All Functor (Remove (Pred (Len lcs)) lcs)
     , All Functor (Remove (Pred (Len rcs)) rcs)
     , Functor m
     )
  => Node lcs m a
  -> Node rcs m a
  -> Node (Remove (Pred (Len rcs)) rcs ++ Remove (Pred (Len lcs)) lcs) m a
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
     forall n k lcs lc rcs rc m r.
     ( Known Length (Remove n lcs)
     , All Functor (Remove n lcs)
     , All Functor (Remove k rcs)
     , Annihilate rc lc
     , Functor m
     )
  => IIndex n lcs lc -- ^ The index of the linked channel on the first node.
  -> IIndex k rcs rc -- ^ The index of the linked channel on the
     -- second node.
  -> Node lcs m r
  -> Node rcs m r
  -> Node (Remove n lcs ++ Remove k rcs) m r
linkOn n k =
  genericLinkOn (fmap Identity) Identity (finl proxyR) (finr proxyL) n k .
  Identity
  where
    proxyR = Proxy :: Proxy (Remove k rcs)
    proxyL = Proxy :: Proxy (Remove n lcs)

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
     forall n k lcs lc rcs rc m r.
     ( Known Length (Remove k rcs)
     , All Functor (Remove n lcs)
     , All Functor (Remove k rcs)
     , Annihilate rc lc
     , Functor m
     )
  => IIndex n lcs lc -- ^ The index of the linked channel on the first node.
  -> IIndex k rcs rc -- ^ The index of the linked channel on the
     -- second node.
  -> Node lcs m r
  -> Node rcs m r
  -> Node (Remove k rcs ++ Remove n lcs) m r
linkOn' n k =
  genericLinkOn (fmap Identity) Identity (finr proxyR) (finl proxyL) n k .
  Identity
  where
    proxyR = Proxy :: Proxy (Remove k rcs)
    proxyL = Proxy :: Proxy (Remove n lcs)

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
     forall lcs lreq lresp rcs' rreq rresp m a.
     ( Known Length lcs
     , Null lcs ~ 'False
     , All Functor (Remove (Pred (Len lcs)) lcs)
     , All Functor rcs'
     , Last lcs ~ Compose lresp lreq
     , Annihilate lreq rresp
     , Annihilate rreq lresp
     , Functor m
     )
  => lreq (Node lcs m a) -- ^ Upstream ‘server’ node.
  -> Node (Compose rresp rreq : rcs') m a -- ^ Downstream ‘client’
                                          -- node.
  -> Node (Remove (Pred (Len lcs)) lcs ++ rcs') m a
(+>>) = linkDuplexPullPipe_ \\ iwithoutRetainsLength lidx
  where
    lidx :: IIndex (Pred (Len lcs)) lcs (Last lcs)
    lidx = lastIndex

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
     ( Known Length lcs
     , Null lcs ~ 'False
     , All Functor (Remove (Pred (Len lcs)) lcs)
     , All Functor rcs'
     , Last lcs ~ Compose lresp lreq
     , Annihilate lreq rresp
     , Annihilate rreq lresp
     , Functor rreq'
     , Functor m
     )
  => lreq (Node lcs m a) -- ^ Upstream ‘server’ node.
  -> rreq' (Node (Compose rresp rreq : rcs') m a) -- ^ Downstream
     -- ‘client’ node.
  -> rreq' (Node (Remove (Pred (Len lcs)) lcs ++ rcs') m a)
(>+>) left = fmap (left +>>)

infixl 6 >+>

linkDuplexPullPipe_ ::
     ( All Functor (Remove (Pred (Len lcs)) lcs)
     , All Functor rcs'
     , Null lcs ~ 'False
     , Known Length lcs
     , Known Length (Remove (Pred (Len lcs)) lcs)
     , Last lcs ~ Compose lresp lreq
     , Annihilate lreq rresp
     , Annihilate rreq lresp
     , Functor m
     )
  => lreq (Node lcs m r)
  -> Node (Compose rresp rreq : rcs') m r
  -> Node (Remove (Pred (Len lcs)) lcs ++ rcs') m r
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
     forall lcs lreq lresp rcs' rreq rresp m a.
     ( Known Length lcs
     , Null lcs ~ 'False
     , All Functor (Remove (Pred (Len lcs)) lcs)
     , All Functor rcs'
     , Last lcs ~ Compose lresp lreq
     , Annihilate lreq rresp
     , Annihilate rreq lresp
     , Functor m
     )
  => Node lcs m a -- ^ Upstream ‘client’ node.
  -> rreq (Node (Compose rresp rreq : rcs') m a) -- ^ Downstream
     -- ‘server’ node.
  -> Node (Remove (Pred (Len lcs)) lcs ++ rcs') m a
(>>~) = linkDuplexPushPipe_ \\ iwithoutRetainsLength lidx
  where
    lidx :: IIndex (Pred (Len lcs)) lcs (Last lcs)
    lidx = lastIndex

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
     ( Known Length lcs
     , Null lcs ~ 'False
     , All Functor (Remove (Pred (Len lcs)) lcs)
     , All Functor rcs'
     , Functor lreq'
     , Last lcs ~ Compose lresp lreq
     , Annihilate lreq rresp
     , Annihilate rreq lresp
     , Functor m
     )
  => lreq' (Node lcs m a) -- ^ Upstream ‘client’ node.
  -> rreq (Node (Compose rresp rreq : rcs') m a) -- ^ Downstream
     -- ‘server’ node.
  -> lreq' (Node (Remove (Pred (Len lcs)) lcs ++ rcs') m a)
left >~> right = fmap (>>~ right) left

infixl 6 >~>

linkDuplexPushPipe_ ::
     ( All Functor (Remove (Pred (Len lcs)) lcs)
     , All Functor rcs'
     , Null lcs ~ 'False
     , Known Length lcs
     , Known Length (Remove (Pred (Len lcs)) lcs)
     , Last lcs ~ Compose lresp lreq
     , Annihilate lreq rresp
     , Annihilate rreq lresp
     , Functor m
     )
  => Node lcs m r
  -> rreq (Node (Compose rresp rreq : rcs') m r)
  -> Node (Remove (Pred (Len lcs)) lcs ++ rcs') m r
linkDuplexPushPipe_ = flip (linkOnDuplex' i0 lastIndex)

-- | @('|>~')@ is to @('>>~')@ what @('|->')@ is to @('>->')@.
(|>~) ::
     ( All Functor lcs
     , All Functor rcs
     , Known Length rcs
     , Annihilate lreq rresp
     , Annihilate rreq lresp
     , Functor m
     )
  => Node (Compose lresp lreq : lcs) m r -- ^ A ‘client’ node.
  -> rreq (Node (Compose rresp rreq : rcs) m r) -- ^ A ‘server’ node.
  -> Node (rcs ++ lcs) m r
(|>~) = flip (linkOnDuplex i0 i0)

infixl 4 |>~

-- | @('+>|')@ is to @('+>>')@ what @('>-|')@ is to @('>->')@.
(+>|) ::
     forall lcs rcs lreq lresp rresp rreq m a.
     ( Known Length lcs
     , Known Length rcs
     , Null lcs ~ 'False
     , Null rcs ~ 'False
     , All Functor (Remove (Pred (Len lcs)) lcs)
     , All Functor (Remove (Pred (Len rcs)) rcs)
     , Last lcs ~ Compose lresp lreq
     , Last rcs ~ Compose rresp rreq
     , Annihilate lreq rresp
     , Annihilate rreq lresp
     , Functor m
     )
  => lreq (Node lcs m a) -- ^ A ‘server’ node.
  -> Node rcs m a -- ^ A ‘client’ node.
  -> Node (Remove (Pred (Len rcs)) rcs ++ Remove (Pred (Len lcs)) lcs) m a
(+>|) = linkConsumerDuplex_ \\ iwithoutRetainsLength ridx
  where
    ridx :: IIndex (Pred (Len rcs)) rcs (Last rcs)
    ridx = lastIndex

infixr 4 +>|

linkConsumerDuplex_ ::
     ( Known Length lcs
     , Known Length rcs
     , Known Length (Remove (Pred (Len rcs)) rcs)
     , All Functor (Remove (Pred (Len lcs)) lcs)
     , All Functor (Remove (Pred (Len rcs)) rcs)
     , Null lcs ~ 'False
     , Null rcs ~ 'False
     , Last lcs ~ Compose lresp lreq
     , Last rcs ~ Compose rresp rreq
     , Annihilate lreq rresp
     , Annihilate rreq lresp
     , Functor m
     )
  => lreq (Node lcs m a)
  -> Node rcs m a
  -> Node (Remove (Pred (Len rcs)) rcs ++ Remove (Pred (Len lcs)) lcs) m a
linkConsumerDuplex_ = linkOnDuplex' lastIndex lastIndex

-- | Link nodes on a specified pair of duplex channels, putting first
-- (‘server’) node's channels first in the result.
linkOnDuplex ::
     forall n k lcs lresp lreq rcs rresp rreq m r.
     ( Known Length (Remove n lcs)
     , All Functor (Remove n lcs)
     , All Functor (Remove k rcs)
     , Annihilate lreq rresp
     , Annihilate rreq lresp
     , Functor m
     )
  => IIndex n lcs (Compose lresp lreq) -- ^ The index of the linked
     -- channel on the ‘server’ node.
  -> IIndex k rcs (Compose rresp rreq) -- ^ The index of the linked
     -- channel on the ‘client’ node.
  -> lreq (Node lcs m r) -- ^ ‘Server’ node.
  -> Node rcs m r -- ^ ‘Client’ node.
  -> Node (Remove n lcs ++ Remove k rcs) m r
linkOnDuplex = genericLinkOn getCompose getCompose (finl proxyR) (finr proxyL)
  where
    proxyR :: Proxy (Remove k rcs)
    proxyR = Proxy
    proxyL :: Proxy (Remove n lcs)
    proxyL = Proxy

-- | Link nodes on a specified pair of duplex channels, putting second
-- (‘client’) node's channels first in the result.
linkOnDuplex' ::
     forall n k lcs lresp lreq rcs rresp rreq m r.
     ( Known Length (Remove k rcs)
     , All Functor (Remove n lcs)
     , All Functor (Remove k rcs)
     , Annihilate lreq rresp
     , Annihilate rreq lresp
     , Functor m
     )
  => IIndex n lcs (Compose lresp lreq) -- ^ The index of the linked
     -- channel on the ‘server’ node.
  -> IIndex k rcs (Compose rresp rreq) -- ^ The index of the linked
     -- channel on the ‘client’ node.
  -> lreq (Node lcs m r) -- ^ ‘Server’ node.
  -> Node rcs m r -- ^ ‘Client’ node.
  -> Node (Remove k rcs ++ Remove n lcs) m r
linkOnDuplex' = genericLinkOn getCompose getCompose (finr proxyR) (finl proxyL)
  where
    proxyR :: Proxy (Remove k rcs)
    proxyR = Proxy
    proxyL :: Proxy (Remove n lcs)
    proxyL = Proxy

-- | The most generic linking function, used to implement all other
-- function in this module.  Calling it directly is practically never
-- needed.
genericLinkOn ::
     ( All Functor (Remove n lcs)
     , All Functor (Remove k rcs)
     , Annihilate lreq rresp
     , Annihilate rreq lresp
     , Functor m
     )
  => (forall x. lc x -> lresp (lreq x)) -- ^ Convert the channel on
     -- the first node to a duplex representation.
  -> (forall x. rc x -> rresp (rreq x)) -- ^ Convert the channel on
     -- the second node to a duplex representation.
  -> (forall x. FSum (Remove n lcs) x -> FSum rescs x) -- ^ Embed remaining
     -- channels of the first node into the resulting list.
  -> (forall x. FSum (Remove k rcs) x -> FSum rescs x) -- ^ Embed remaining
     -- channels of the second node into the resulting list.
  -> IIndex n lcs lc -- ^ The index of the linked channel on the first
                     -- node.
  -> IIndex k rcs rc -- ^ The index of the linked channel on the
                     -- second node.
  -> lreq (Node lcs m r)
  -> Node rcs m r
  -> Node rescs m r
genericLinkOn ldecompose rdecompose lembed rembed n k = loop
  where
    loop left right =
      Node $
      case getNode right of
        ReturnF r -> ReturnF r
        EffectF eff -> EffectF (fmap (loop left) eff)
        ConnectF cons ->
          case fdecompIdx k cons of
            Left other -> ConnectF (rembed (fmap (loop left) other))
            Right con ->
              -- The case statements are here for strictness; the
              -- point is to avoid accidentally retaining the
              -- reference to the node we're iterating over.
              case annihilate left (rdecompose con) of
                (left', right') -> getNode $ loop' right' left'
    loop' right left =
      Node $
      case getNode left of
        ReturnF r -> ReturnF r
        EffectF eff -> EffectF (fmap (loop' right) eff)
        ConnectF cons ->
          case fdecompIdx n cons of
            Left other -> ConnectF (lembed (fmap (loop' right) other))
            Right con ->
              case annihilate right (ldecompose con) of
                (right', left') -> getNode $ loop left' right'
