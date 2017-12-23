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
functor-generic functions (e.g. 'gforOn') or functions in this module.
-}
{-# OPTIONS_HADDOCK show-extensions #-}
{-# LANGUAGE BangPatterns #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE GADTs #-}
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
import Cobweb.Core
  ( Leaf
  , Producer
  , Yield(Yield)
  , connect
  , gforOn
  , i0
  , yieldOn
  )
import Cobweb.Internal (build, unconsNode)
import qualified Cobweb.Producer as P
import Cobweb.Type.Combinators (FSum(FInL), fsumOnly)

-- | Split a stream into substreams of the specified number of
-- elements each (except, possibly, for the last one).
--
-- Semantics of this function are 'Producer'-oriented; that is, each
-- chunk contains all effects /preceding/ its connections (except for
-- the first one), which typically makes sense for 'Producer's, which
-- run all connection-associated actions before the actual connection.
chunkBy :: HasCallStack => Int -> Leaf c m a -> Leaf (Leaf c m) m a
chunkBy n node
  | n <= 0 = error "Chunk length should be positive"
  | otherwise =
    build
      (\ret con lft ->
         let loop =
               unconsNode
                 ret
                 (\c cont -> con (FInL $ P.splitAt n (connect c >>= cont)) loop)
                 (\e cont -> lft e (loop . cont))
         in loop node)

-- | Split a stream into substreams of specified number of connections
-- each (except, possibly, for the last one).
--
-- Semantics of this function are 'Cobweb.Core.Consumer'-oriented;
-- that is, each chunk contains all effects /following/ its
-- connections, which typically makes sense for
-- 'Cobweb.Core.Consumer's, which run all connection-associated
-- actions after the actual connection.
chunkConsumerBy :: HasCallStack => Int -> Leaf c m r -> Leaf (Leaf c m) m r
chunkConsumerBy n node
  | n <= 0 = error "Chunk length should be positive"
  | otherwise =
    build
      (\ret con lft ->
         let loop =
               unconsNode
                 ret
                 (\c cont -> con (FInL $ C.splitAt n (connect c >>= cont)) loop)
                 (\e cont -> lft e (loop . cont))
         in loop node)

-- | Groups consecutive equal (as identified by the supplied
-- predicate) elements of the stream together.
--
-- Supplied predicate should define [an equivalence
-- relation](https://en.wikipedia.org/wiki/Equivalence_relation#Definition).
groupBy :: (a -> a -> Bool) -> Producer a m r -> Leaf (Producer a m) m r
groupBy eq node =
  build
    (\ret con lft ->
       let loop =
             unconsNode
               ret
               (\c cont ->
                  let !(Yield a) = fsumOnly c
                  in con (FInL $ connect c >>= (P.span (eq a) . cont)) loop)
               (\e cont -> lft e (loop . cont))
       in loop node)

-- | Groups consecutive equal stream elements together.
--
-- @
-- 'Cobweb.Group.group' = 'Cobweb.Group.groupBy' ('==')
-- @
group :: Eq a => Producer a m r -> Leaf (Producer a m) m r
group = groupBy (==)

-- | Concatenate all substreams together, similar to
-- 'Data.List.concat'.
--
-- This essentially inverses the effects of the grouping functions in
-- this module.
--
-- @
-- 'Cobweb.Group.concat' node = 'gforOn' 'i0' node 'id'
-- @
concat :: Leaf (Leaf c m) m r -> Leaf c m r
concat node = gforOn i0 node id

-- | Concatenate substreams together, inserting separator between
-- them.  A moral equivalent of 'Data.List.intercalate'.
intercalate ::
     forall c m a. Monad m
  => Leaf c m () -- ^ Separator.
  -> Leaf (Leaf c m) m a -- ^ Stream of streams.
  -> Leaf c m a
intercalate separator = loop
  where
    loop =
      unconsNode
        pure
        (\c cont -> fsumOnly c >>= (loop' . cont))
        (\e cont -> lift e >>= (loop . cont))
    loop' :: Leaf (Leaf c m) m r -> Leaf c m r
    loop' node = gforOn i0 node (separator >>)

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
     Monad m
  => (forall x. Leaf c m x -> m (a, x))
  -> Leaf (Leaf c m) m r
  -> Producer a m r
foldChunks reducer node =
  gforOn i0 node $ \chunk -> do
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
-- 'Cobweb.Core.Tube' ('Cobweb.Core.Await' i) ('Cobweb.Pipe.Pipe' i o) m r
-- @
--
-- But now some of the 'Cobweb.Consumer.await's are ‘hidden’ in the
-- second channel, and 'Cobweb.Core.Node's linking to the chunked
-- 'Cobweb.Pipe.Pipe' on the first channel will skip them, which is
-- clearly not what we want.
