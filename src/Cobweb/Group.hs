{-|
Module: Cobweb.Group
Description: Group streams into substreams.
Copyright: 2017 © Ivan Timokhin
License: BSD3
Maintainer: timokhin.iv@gmail.com
Stability: experimental

Grouping values in a streaming context while retaining streaming is
somewhat tricky; the approach taken by this module, following
@streaming@ and @pipes-group@ libraries, is to use the type of the
substream—@'Leaf' c m@—as the connection functor itself.  That way,
the type of the ‘stream of streams’ is @'Leaf' ('Leaf' c m) m r@.
Here, each connection represents a single substream.

Unfortunately, this means that such nested streams can no longer be
linked together via "Cobweb.Link", and need to be processed via
functor-generic functions (e.g. 'forsOn') or functions in this module.
-}
{-# OPTIONS_HADDOCK show-extensions #-}
{-# LANGUAGE BangPatterns #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE ScopedTypeVariables #-}

module Cobweb.Group
  (
    -- * Grouping elements
    chunkBy
  , chunkConsumerBy
  , groupBy
  , group
    -- * Flattening substreams
  , Cobweb.Group.concat
  , intercalate
  , foldChunks
    -- * Why 'Leaf'?
    -- $leaf
  ) where

import Control.Monad.Trans (lift)
import GHC.Stack (HasCallStack)

import qualified Cobweb.Consumer as C
import Cobweb.Core (Leaf, Producer, forsOn, i0, yieldOn)
import Cobweb.Internal
       (Node(Node, getNode), NodeF(ConnectF, EffectF, ReturnF))
import qualified Cobweb.Producer as P
import Cobweb.Type.Combinators (FSum(FInL), fsumOnly)

-- | Split a stream into substreams of the specified number of
-- elements each (except, possibly, for the last one).
--
-- Semantics of this function are 'Producer'-oriented; that is, each
-- chunk contains all effects /preceding/ its connections (except for
-- the first one), which typically makes sense for 'Producer's, which
-- run all connection-associated actions before the actual connection.
chunkBy ::
     (HasCallStack, Functor c, Functor m)
  => Int
  -> Leaf c m r
  -> Leaf (Leaf c m) m r
chunkBy n
  | n <= 0 = error "Chunk length should be positive"
  | otherwise = loop
  where
    loop node =
      Node $
      case getNode node of
        ReturnF r -> ReturnF r
        EffectF eff -> EffectF (fmap loop eff)
        ConnectF _ -> ConnectF $ FInL $ fmap loop (P.splitAt n node)

-- | Split a stream into substreams of specified number of connections
-- each (except, possibly, for the last one).
--
-- Semantics of this function are 'Cobweb.Core.Consumer'-oriented;
-- that is, each chunk contains all effects /following/ its
-- connections, which typically makes sense for
-- 'Cobweb.Core.Consumer's, which run all connection-associated
-- actions after the actual connection.
chunkConsumerBy ::
     (HasCallStack, Functor c, Functor m)
  => Int
  -> Leaf c m r
  -> Leaf (Leaf c m) m r
chunkConsumerBy n
  | n <= 0 = error "Chunk length should be positive"
  | otherwise = loop
  where
    loop node =
      Node $
      case getNode node of
        ReturnF r -> ReturnF r
        EffectF eff -> EffectF (fmap loop eff)
        ConnectF _ -> ConnectF $ FInL $ fmap loop (C.splitAt n node)

-- | Groups consecutive equal (as identified by the supplied
-- predicate) elements of the stream together.
--
-- Supplied predicate should define [an equivalence
-- relation](https://en.wikipedia.org/wiki/Equivalence_relation#Definition).
groupBy ::
     Functor m => (a -> a -> Bool) -> Producer a m r -> Leaf (Producer a m) m r
groupBy eq = loop
  where
    loop node =
      Node $
      case getNode node of
        ReturnF r -> ReturnF r
        EffectF eff -> EffectF (fmap loop eff)
        ConnectF con ->
          let !(a, rest) = fsumOnly con
          in ConnectF $
             FInL $ Node $ ConnectF $ FInL (a, fmap loop (P.span (eq a) rest))

-- | Groups consecutive equal stream elements together.
--
-- @
-- 'Cobweb.Group.group' = 'Cobweb.Group.groupBy' ('==')
-- @
group :: (Eq a, Functor m) => Producer a m r -> Leaf (Producer a m) m r
group = groupBy (==)

-- | Concatenate all substreams together, similar to
-- 'Data.List.concat'.
--
-- This essentially inverses the effects of the grouping functions in
-- this module.
--
-- @
-- 'Cobweb.Group.concat' node = 'forsOn' 'i0' node 'id'
-- @
concat :: (Functor c, Functor m) => Leaf (Leaf c m) m r -> Leaf c m r
concat node = forsOn i0 node id

-- | Concatenate substreams together, inserting separator between
-- them.  A moral equivalent of 'Data.List.intercalate'.
intercalate ::
     forall c m r. (Functor c, Functor m)
  => Leaf c m () -- ^ Separator.
  -> Leaf (Leaf c m) m r -- ^ Stream of streams.
  -> Leaf c m r
intercalate separator = loop
  where
    loop :: Leaf (Leaf c m) m r -> Leaf c m r
    loop node =
      Node $
      case getNode node of
        ReturnF r -> ReturnF r
        EffectF eff -> EffectF (fmap loop eff)
        ConnectF con -> getNode $ fsumOnly con >>= loop'
    loop' :: Leaf (Leaf c m) m r -> Leaf c m r
    loop' node = forsOn i0 node (separator >>)

-- | Fold contents of each chunk individually, and stream results.
--
-- The interface is designed to be used with "Cobweb.Fold" module.
--
-- ====__Example__
--
-- @
-- 'Cobweb.Fold.toListN_' '$' 'foldChunks' 'Cobweb.Fold.toListN' '$' 'chunkBy' 4 '$' 'Cobweb.Producer.each' [1..10]
-- @
--
-- produces
--
-- > [[1,2,3,4],[5,6,7,8],[9,10]]
--
-- Keep in mind that accumulation into lists is there only for
-- demonstration purposes; actually doing that is usually a bad idea.
foldChunks ::
     (Functor c, Monad m)
  => (forall x. Leaf c m x -> m (a, x))
  -> Leaf (Leaf c m) m r
  -> Producer a m r
foldChunks reducer node =
  forsOn i0 node $ \chunk -> do
    (a, x) <- lift $ reducer chunk
    yieldOn i0 a
    pure x

-- $leaf
--
-- While it is technically possible to group 'Cobweb.Core.Node's with any
-- number of channels this way, semantics of the result get weird
-- quickly.
--
-- Consider 'Cobweb.Pipe.Pipe' for example.  Naively, the type of a
-- 'Cobweb.Pipe.Pipe' chunked on the second channel would be something
-- like
--
-- @
-- 'Cobweb.Core.Tube' ('Cobweb.Core.Awaiting' i) ('Cobweb.Pipe.Pipe' i o) m r
-- @
--
-- But now some of the 'Cobweb.Consumer.await's are ‘hidden’ in the
-- second channel, and 'Cobweb.Core.Node's linking to the chunked
-- 'Cobweb.Pipe.Pipe' on the first channel will skip them, which is
-- clearly not what we want.
