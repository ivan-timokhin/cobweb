{-|
Module: Cobweb.Fold
Description: Folding 'Producer's
Copyright: 2017 © Ivan Timokhin
License: BSD3
Maintainer: timokhin.iv@gmail.com
Stability: experimental

Functions that fold over a 'Producer'.

Folding functions are designed to be used with the @foldl@ library.
For example,

@
Control.Foldl.purely 'foldNode' :: Fold a b -> Producer a m r -> m (b, r)
Control.Foldl.impurely 'foldMNode' :: FoldM a b -> Producer a m r -> m (b, r)
@

However, they can certainly be used by themselves.

Note that this module support almost exclusively strict left folds, so
that the whole process happens in constant space.
-}
{-# LANGUAGE BangPatterns #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE ScopedTypeVariables #-}

module Cobweb.Fold
  (
    -- * Complete generic folds
    foldNode
  , foldNode_
  , foldMNode
  , foldMNode_
    -- * Incomplete folds
  , foldOn
  , foldOn_
  , foldMOn
  , foldMOn_
    -- * Scans
  , scanOn
  , scanOnM
    -- * Collecting to list
    -- $list
  , toListN
  , toListN_
  ) where

import Control.Monad.Trans (lift)
import Data.Proxy (Proxy(Proxy))

import Cobweb.Core (Producer, Yielding, run, yieldOn)
import Cobweb.Internal
       (Node(Node, getNode), NodeF(ConnectF, EffectF, ReturnF))
import Cobweb.Type.Combinators
       (All, IIndex, Remove, Replace, fdecompIdx, fdecompReplaceIdx, i0,
        replaceIdx)

-- | Fold over values from a 'Producer', and provide both the fold
-- result and the 'Producer' return value.
foldNode ::
     Monad m
  => (x -> a -> x) -- ^ Combining function.
  -> x -- ^ Seed value.
  -> (x -> b) -- ^ Finalise accumulator (typically 'id' in manual
              -- use).
  -> Producer a m r -- ^ Source of values; essentially an effectful
                    -- list.
  -> m (b, r)
foldNode comb seed fin = run . foldOn i0 comb seed fin

-- | Same as 'foldNode', but discard 'Producer' return value.
foldNode_ :: Monad m => (x -> a -> x) -> x -> (x -> b) -> Producer a m r -> m b
foldNode_ comb seed fin = fmap fst . foldNode comb seed fin

-- | Fold over values from a 'Producer', possibly with effects in the
-- base monad, and provide both the fold result and the 'Producer'
-- return value.
--
-- __Note:__ the action for seed is always run first, prior to
-- anything in the 'Producer'.
foldMNode ::
     Monad m
  => (x -> a -> m x) -- ^ Combining function.
  -> m x -- ^ Action yielding a seed value.
  -> (x -> m b) -- ^ Finalise accumulator (e.g. 'pure').
  -> Producer a m r
  -> m (b, r)
foldMNode comb seed fin = run . foldMOn i0 comb seed fin

-- | Same as 'foldMNode', but discard 'Producer' return value.
foldMNode_ ::
     Monad m => (x -> a -> m x) -> m x -> (x -> m b) -> Producer a m r -> m b
foldMNode_ comb seed fin = fmap fst . foldMNode comb seed fin

-- | Fold over values provided on one of the 'Node' channels, and add
-- the result to the return value.
foldOn ::
     (Functor m, All Functor (Remove n cs))
  => IIndex n cs (Yielding a) -- ^ The index of the channel to fold
                              -- over.
  -> (x -> a -> x) -- ^ Combining function.
  -> x -- ^ Seed.
  -> (x -> b) -- ^ Finalise accumulator.
  -> Node cs m r
  -> Node (Remove n cs) m (b, r)
foldOn n comb seed fin = loop seed
  where
    loop !z (Node node) =
      Node $
      case node of
        ReturnF r -> ReturnF (fin z, r)
        EffectF eff -> EffectF (fmap (loop z) eff)
        ConnectF con ->
          case fdecompIdx n con of
            Right (a, rest) -> getNode $ loop (comb z a) rest
            Left other -> ConnectF (fmap (loop z) other)

-- | Same as 'foldOn', but discard original return value.
foldOn_ ::
     (Functor m, All Functor (Remove n cs))
  => IIndex n cs (Yielding a)
  -> (x -> a -> x)
  -> x
  -> (x -> b)
  -> Node cs m r
  -> Node (Remove n cs) m b
foldOn_ n comb seed fin = fmap fst . foldOn n comb seed fin

-- | Same as 'foldOn', but with effects in the base monad.
--
-- __Note:__ the action for seed is always run first, prior to
-- anything in the 'Node'.
foldMOn ::
     (Functor m, All Functor (Remove n cs))
  => IIndex n cs (Yielding a)
  -> (x -> a -> m x)
  -> m x
  -> (x -> m b)
  -> Node cs m r
  -> Node (Remove n cs) m (b, r)
foldMOn n comb seed fin node' = Node (EffectF (fmap (flip loop node') seed))
  where
    loop !z (Node node) =
      Node $
      case node of
        ReturnF r -> EffectF (fmap (\b -> pure (b, r)) (fin z))
        EffectF eff -> EffectF (fmap (loop z) eff)
        ConnectF con ->
          case fdecompIdx n con of
            Left other -> ConnectF (fmap (loop z) other)
            Right (a, rest) -> EffectF (fmap (flip loop rest) (comb z a))

-- | Same as 'foldMOn', but discard original return value.
foldMOn_ ::
     (Functor m, All Functor (Remove n cs))
  => IIndex n cs (Yielding a)
  -> (x -> a -> m x)
  -> m x
  -> (x -> m b)
  -> Node cs m r
  -> Node (Remove n cs) m b
foldMOn_ n comb seed fin = fmap fst . foldMOn n comb seed fin

-- | Strict left scan of a 'Node' on one of the channels
-- (cf. 'Data.List.scanl').
--
-- The channel producing intermediate values is substituted in-place
-- for the channel being folded.
--
-- __Note:__ seed is always yielded first, before running any action
-- from the original node.  In general, values are yielded as soon as
-- they become available.
--
-- ====__Signatures for some specific indices__
-- @
-- 'scanOn' 'i0' ::
--      ('Functor' m, 'All' 'Functor' cs)
--   => (x -> a -> x)
--   -> x
--   -> (x -> b)
--   -> 'Node' ('Yielding' a : cs) m r
--   -> 'Node' ('Yielding' b : cs) m r
--
-- 'scanOn' 'Cobweb.Core.i1' ::
--      ('Functor' m, 'Functor' c0, 'All' 'Functor' cs)
--   => (x -> a -> x)
--   -> x
--   -> (x -> b)
--   -> 'Node' (c0 : 'Yielding' a : cs) m r
--   -> 'Node' (c0 : 'Yielding' b : cs) m r
--
-- 'scanOn' 'Cobweb.Core.i2' ::
--      ('Functor' m, 'Functor' c0, 'Functor' c1, 'All' 'Functor' cs)
--   => (x -> a -> x)
--   -> x
--   -> (x -> b)
--   -> 'Node' (c0 : c1 : 'Yielding' a : cs) m r
--   -> 'Node' (c0 : c1 : 'Yielding' b : cs) m r
-- @
scanOn ::
     forall m cs n x a b r. (Functor m, All Functor (Replace n cs (Yielding b)))
  => IIndex n cs (Yielding a) -- ^ Index of the channel to scan over.
  -> (x -> a -> x) -- ^ Combining function.
  -> x -- ^ Seed.
  -> (x -> b) -- ^ Finalise accumulator (evaluated at every step to
     -- produce yielded value).
  -> Node cs m r
  -> Node (Replace n cs (Yielding b)) m r
scanOn n comb seed fin = (yieldOn n' (fin seed) >>) . loop seed
  where
    n' = replaceIdx n
    loop !z (Node node) =
      Node $
      case node of
        ReturnF r -> ReturnF r
        EffectF eff -> EffectF (fmap (loop z) eff)
        ConnectF con ->
          case fdecompReplaceIdx n (Proxy :: Proxy (Yielding b)) con of
            Left other -> ConnectF (fmap (loop z) other)
            Right (a, rest) ->
              getNode $ do
                let !z' = comb z a
                yieldOn n' (fin z')
                loop z' rest

-- | Same as 'scanOn', but with possible effects in the base monad.
--
-- __Note:__ like in 'scanOn', values are yielded as soon as
-- possible.  In particular, seed is evaluated and yielded before
-- running anything in the original 'Node'.
--
-- ====__Signatures for some specific indices__
-- @
-- 'scanOnM' 'i0' ::
--      ('Monad' m, 'All' 'Functor' cs)
--   => (x -> a -> m x)
--   -> m x
--   -> (x -> m b)
--   -> 'Node' ('Yielding' a : cs) m r
--   -> 'Node' ('Yielding' b : cs) m r
--
-- 'scanOnM' 'Cobweb.Core.i1' ::
--      ('Monad' m, 'Functor' c0, 'All' 'Functor' cs)
--   => (x -> a -> m x)
--   -> m x
--   -> (x -> m b)
--   -> 'Node' (c0 : 'Yielding' a : cs) m r
--   -> 'Node' (c0 : 'Yielding' b : cs) m r
--
-- 'scanOnM' 'Cobweb.Core.i2' ::
--      ('Monad' m, 'Functor' c0, 'Functor' c1, 'All' 'Functor' cs)
--   => (x -> a -> m x)
--   -> m x
--   -> (x -> m b)
--   -> 'Node' (c0 : c1 : 'Yielding' a : cs) m r
--   -> 'Node' (c0 : c1 : 'Yielding' b : cs) m r
-- @
scanOnM ::
     forall m cs n x a b r. (Monad m, All Functor (Replace n cs (Yielding b)))
  => IIndex n cs (Yielding a) -- ^ Index of the channel to scan over.
  -> (x -> a -> m x) -- ^ Combining function.
  -> m x -- ^ Seed.
  -> (x -> m b) -- ^ Finalising function (called for each intermediate
                -- result).
  -> Node cs m r
  -> Node (Replace n cs (Yielding b)) m r
scanOnM n comb seed fin node = do
  !seed' <- lift seed
  b <- lift $ fin seed'
  yieldOn n' b
  loop seed' node
  where
    n' = replaceIdx n
    loop !z (Node node') =
      Node $
      case node' of
        ReturnF r -> ReturnF r
        EffectF eff -> EffectF (fmap (loop z) eff)
        ConnectF con ->
          case fdecompReplaceIdx n (Proxy :: Proxy (Yielding b)) con of
            Left other -> ConnectF (fmap (loop z) other)
            Right (a, rest) ->
              getNode $ do
                !z' <- lift $ comb z a
                b <- lift $ fin z'
                yieldOn n' b
                loop z' rest

-- $list
--
-- __Do not use these in production code!__
--
-- These functions do not reflect intended usage of this library, and
-- are provided only to simplify testing.

-- | Gather yielded values into a list.
toListN :: Monad m => Producer a m r -> m ([a], r)
toListN = foldNode (\diff a -> diff . (a :)) id ($ [])

-- | Gather yielded values into a list, and throw away return value.
toListN_ :: Monad m => Producer a m r -> m [a]
toListN_ = fmap fst . toListN
