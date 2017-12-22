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

import Data.Proxy (Proxy(Proxy))

import Cobweb.Core (Producer, Yield)
import Cobweb.Internal (Node, cata, build)
import Cobweb.Type.Combinators
  ( IIndex
  , Remove
  , Replace
  , fdecompIdx
  , fdecompReplaceIdx
  , finjectIdx
  , fsumOnly
  , replaceIdx
  )

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
foldNode comb !seed fin node =
  cata
    (\r !x -> pure (fin x, r))
    (\c cont !x ->
       case fsumOnly c of
         (a, y) ->
           let !x' = x `comb` a
           in cont y x')
    (\e cont !x -> e >>= (`cont` x))
    node
    seed

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
foldMNode comb seed fin node = do
  !z <- seed
  cata
    (\r !x -> do
       !b <- fin x
       pure (b, r))
    (\c cont !x ->
       case fsumOnly c of
         (a, y) -> do
           !x' <- x `comb` a
           cont y x')
    (\e cont !x -> e >>= (`cont` x))
    node
    z

-- | Same as 'foldMNode', but discard 'Producer' return value.
foldMNode_ ::
     Monad m => (x -> a -> m x) -> m x -> (x -> m b) -> Producer a m r -> m b
{-# INLINE foldMNode_ #-}
foldMNode_ comb seed fin = fmap fst . foldMNode comb seed fin

-- | Fold over values provided on one of the 'Node' channels, and add
-- the result to the return value.
foldOn ::
     Remove n cs cs'
  => IIndex n cs (Yield a) -- ^ The index of the channel to fold
                              -- over.
  -> (x -> a -> x) -- ^ Combining function.
  -> x -- ^ Seed.
  -> (x -> b) -- ^ Finalise accumulator.
  -> Node cs m r
  -> Node cs' m (b, r)
{-# INLINE foldOn #-}
foldOn n comb !seed fin node =
  build
    (\ret con lft ->
       cata
         (\r !x -> ret (fin x, r))
         (\c cont !x ->
            case fdecompIdx n c of
              Right (a, y) ->
                let !x' = x `comb` a
                in cont y x'
              Left other -> con other (`cont` x))
         (\e cont !x -> lft e (`cont` x))
         node
         seed)

-- | Same as 'foldOn', but discard original return value.
foldOn_ ::
     Remove n cs cs'
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
     Remove n cs cs'
  => IIndex n cs (Yield a)
  -> (x -> a -> m x)
  -> m x
  -> (x -> m b)
  -> Node cs m r
  -> Node cs' m (b, r)
{-# INLINE foldMOn #-}
foldMOn n comb seed fin node =
  build
    (\ret con lft ->
       lft seed $
       cata
         (\r !x -> lft (fin x) (\ !b -> ret (b, r)))
         (\c cont !x ->
            case fdecompIdx n c of
              Right (a, y) -> lft (x `comb` a) (\ !x' -> cont y x')
              Left other -> con other (`cont` x))
         (\e cont !x -> lft e (`cont` x))
         node)

-- | Same as 'foldMOn', but discard original return value.
foldMOn_ ::
     Remove n cs cs'
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
     forall m cs cs' n x a b r. Replace n cs (Yield b) cs'
  => IIndex n cs (Yield a) -- ^ Index of the channel to scan over.
  -> (x -> a -> x) -- ^ Combining function.
  -> x -- ^ Seed.
  -> (x -> b) -- ^ Finalise accumulator (evaluated at every step to
     -- produce yielded value).
  -> Node cs m r
  -> Node cs' m r
{-# INLINE scanOn #-}
scanOn n comb !seed fin node =
  build
    (\ret con lft ->
       con (finjectIdx n' (fin seed, ())) . const $
       cata
         (\r !_ -> ret r)
         (\c cont !x ->
            case fdecompReplaceIdx n (Proxy :: Proxy (Yield b)) c of
              Left other -> con other (`cont` x)
              Right (a, y) ->
                let !x' = x `comb` a
                in con (finjectIdx n' (fin x', ())) . const $ cont y x')
         (\e cont !x -> lft e (`cont` x))
         node
         seed)
  where
    n' = replaceIdx n

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
     forall m cs cs' n x a b r. Replace n cs (Yield b) cs'
  => IIndex n cs (Yield a) -- ^ Index of the channel to scan over.
  -> (x -> a -> m x) -- ^ Combining function.
  -> m x -- ^ Seed.
  -> (x -> m b) -- ^ Finalising function (called for each intermediate
                -- result).
  -> Node cs m r
  -> Node cs' m r
{-# INLINE scanOnM #-}
scanOnM n comb seed fin node =
  build
    (\ret con lft ->
       lft seed $ \ !seed' ->
         lft (fin seed') $ \b ->
           con (finjectIdx n' (b, ())) . const $
           cata
             (\r !_ -> ret r)
             (\c cont !x ->
                case fdecompReplaceIdx n (Proxy :: Proxy (Yield b)) c of
                  Left other -> con other (`cont` x)
                  Right (a, y) ->
                    lft (x `comb` a) $ \ !x' ->
                      lft (fin x') $ \b' ->
                        con (finjectIdx n' (b', ())) . const $ cont y x')
             (\e cont !x -> lft e (`cont` x))
             node
             seed')
  where
    n' = replaceIdx n

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
