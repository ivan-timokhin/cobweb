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

import Cobweb.Core (Producer, Yield, yieldOn)
import Cobweb.Internal (Node(Connect, Effect, Return))
import Cobweb.Type.Combinators
       (All, IIndex, Remove, Replace, fdecompIdx, fdecompReplaceIdx,
        fsumOnly, replaceIdx)

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
{-# INLINE foldNode #-}
foldNode comb seed fin = loop seed
  where
    loop !z (Return r) = pure (fin z, r)
    loop !z (Effect eff) = do
      rest <- eff
      loop z rest
    loop !z (Connect con) =
      case fsumOnly con of
        (a, rest) -> loop (z `comb` a) rest

-- | Same as 'foldNode', but discard 'Producer' return value.
foldNode_ :: Monad m => (x -> a -> x) -> x -> (x -> b) -> Producer a m r -> m b
{-# INLINE foldNode_ #-}
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
{-# INLINE foldMNode #-}
foldMNode comb seed fin =
  \node -> do
    !z <- seed
    loop z node
  where
    loop !z (Return r) = do
      !b <- fin z
      pure (b, r)
    loop !z (Effect eff) = do
      rest <- eff
      loop z rest
    loop !z (Connect con) =
      case fsumOnly con of
        (a, rest) -> do
          !z' <- z `comb` a
          loop z' rest

-- | Same as 'foldMNode', but discard 'Producer' return value.
foldMNode_ ::
     Monad m => (x -> a -> m x) -> m x -> (x -> m b) -> Producer a m r -> m b
{-# INLINE foldMNode_ #-}
foldMNode_ comb seed fin = fmap fst . foldMNode comb seed fin

-- | Fold over values provided on one of the 'Node' channels, and add
-- the result to the return value.
foldOn ::
     (Functor m, Remove n cs cs', All Functor cs')
  => IIndex n cs (Yield a) -- ^ The index of the channel to fold
                              -- over.
  -> (x -> a -> x) -- ^ Combining function.
  -> x -- ^ Seed.
  -> (x -> b) -- ^ Finalise accumulator.
  -> Node cs m r
  -> Node cs' m (b, r)
{-# INLINE foldOn #-}
foldOn n comb seed fin = loop seed
  where
    loop !z (Return r) = Return (fin z, r)
    loop !z (Effect eff) = Effect (fmap (loop z) eff)
    loop !z (Connect con) =
      case fdecompIdx n con of
        Right (a, rest) -> loop (comb z a) rest
        Left other -> Connect (fmap (loop z) other)

-- | Same as 'foldOn', but discard original return value.
foldOn_ ::
     (Functor m, Remove n cs cs', All Functor cs')
  => IIndex n cs (Yield a)
  -> (x -> a -> x)
  -> x
  -> (x -> b)
  -> Node cs m r
  -> Node cs' m b
{-# INLINE foldOn_ #-}
foldOn_ n comb seed fin = fmap fst . foldOn n comb seed fin

-- | Same as 'foldOn', but with effects in the base monad.
--
-- __Note:__ the action for seed is always run first, prior to
-- anything in the 'Node'.
foldMOn ::
     (Functor m, Remove n cs cs', All Functor cs')
  => IIndex n cs (Yield a)
  -> (x -> a -> m x)
  -> m x
  -> (x -> m b)
  -> Node cs m r
  -> Node cs' m (b, r)
{-# INLINE foldMOn #-}
foldMOn n comb seed fin = \node' -> Effect (fmap (flip loop node') seed)
  where
    loop !z (Return r) = Effect (fmap (\b -> pure (b, r)) (fin z))
    loop !z (Effect eff) = Effect (fmap (loop z) eff)
    loop !z (Connect con) =
      case fdecompIdx n con of
        Left other -> Connect (fmap (loop z) other)
        Right (a, rest) -> Effect (fmap (flip loop rest) (comb z a))

-- | Same as 'foldMOn', but discard original return value.
foldMOn_ ::
     (Functor m, Remove n cs cs', All Functor cs')
  => IIndex n cs (Yield a)
  -> (x -> a -> m x)
  -> m x
  -> (x -> m b)
  -> Node cs m r
  -> Node cs' m b
{-# INLINE foldMOn_ #-}
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
--   -> 'Node' ('Yield' a : cs) m r
--   -> 'Node' ('Yield' b : cs) m r
--
-- 'scanOn' 'Cobweb.Core.i1' ::
--      ('Functor' m, 'Functor' c0, 'All' 'Functor' cs)
--   => (x -> a -> x)
--   -> x
--   -> (x -> b)
--   -> 'Node' (c0 : 'Yield' a : cs) m r
--   -> 'Node' (c0 : 'Yield' b : cs) m r
--
-- 'scanOn' 'Cobweb.Core.i2' ::
--      ('Functor' m, 'Functor' c0, 'Functor' c1, 'All' 'Functor' cs)
--   => (x -> a -> x)
--   -> x
--   -> (x -> b)
--   -> 'Node' (c0 : c1 : 'Yield' a : cs) m r
--   -> 'Node' (c0 : c1 : 'Yield' b : cs) m r
-- @
scanOn ::
     forall m cs cs' n x a b r.
     (Functor m, Replace n cs (Yield b) cs', All Functor cs')
  => IIndex n cs (Yield a) -- ^ Index of the channel to scan over.
  -> (x -> a -> x) -- ^ Combining function.
  -> x -- ^ Seed.
  -> (x -> b) -- ^ Finalise accumulator (evaluated at every step to
     -- produce yielded value).
  -> Node cs m r
  -> Node cs' m r
{-# INLINE scanOn #-}
scanOn n comb seed fin = (yieldOn n' (fin seed) >>) . loop seed
  where
    n' = replaceIdx n
    loop !_ (Return r) = Return r
    loop !z (Effect eff) = Effect (fmap (loop z) eff)
    loop !z (Connect con) =
      case fdecompReplaceIdx n (Proxy :: Proxy (Yield b)) con of
        Left other -> Connect (fmap (loop z) other)
        Right (a, rest) -> do
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
--   -> 'Node' ('Yield' a : cs) m r
--   -> 'Node' ('Yield' b : cs) m r
--
-- 'scanOnM' 'Cobweb.Core.i1' ::
--      ('Monad' m, 'Functor' c0, 'All' 'Functor' cs)
--   => (x -> a -> m x)
--   -> m x
--   -> (x -> m b)
--   -> 'Node' (c0 : 'Yield' a : cs) m r
--   -> 'Node' (c0 : 'Yield' b : cs) m r
--
-- 'scanOnM' 'Cobweb.Core.i2' ::
--      ('Monad' m, 'Functor' c0, 'Functor' c1, 'All' 'Functor' cs)
--   => (x -> a -> m x)
--   -> m x
--   -> (x -> m b)
--   -> 'Node' (c0 : c1 : 'Yield' a : cs) m r
--   -> 'Node' (c0 : c1 : 'Yield' b : cs) m r
-- @
scanOnM ::
     forall m cs cs' n x a b r.
     (Monad m, Replace n cs (Yield b) cs', All Functor cs')
  => IIndex n cs (Yield a) -- ^ Index of the channel to scan over.
  -> (x -> a -> m x) -- ^ Combining function.
  -> m x -- ^ Seed.
  -> (x -> m b) -- ^ Finalising function (called for each intermediate
                -- result).
  -> Node cs m r
  -> Node cs' m r
{-# INLINE scanOnM #-}
scanOnM n comb seed fin =
  \node -> do
    !seed' <- lift seed
    b <- lift $ fin seed'
    yieldOn n' b
    loop seed' node
  where
    n' = replaceIdx n
    loop !_ (Return r) = Return r
    loop !z (Effect eff) = Effect (fmap (loop z) eff)
    loop !z (Connect con) =
      case fdecompReplaceIdx n (Proxy :: Proxy (Yield b)) con of
        Left other -> Connect (fmap (loop z) other)
        Right (a, rest) -> do
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
