{-# LANGUAGE BangPatterns #-}

module Cobweb.Fold where

import Cobweb.Core (Yielding, run)
import Cobweb.Internal
       (Node(Node, getNode), NodeF(ConnectF, EffectF, ReturnF))
import Cobweb.Producer (Producer)
import Cobweb.Type.Combinators
       (All, IIndex, IWithout, fdecompIdx, i0)

foldOn ::
     (Functor m, IWithout n cs cs', All Functor cs')
  => (x -> a -> x)
  -> x
  -> (x -> b)
  -> IIndex n cs (Yielding a)
  -> Node cs m r
  -> Node cs' m (b, r)
foldOn comb seed fin n = loop seed
  where
    loop !z (Node web) =
      Node $
      case web of
        ReturnF r -> ReturnF (fin z, r)
        EffectF eff -> EffectF (fmap (loop z) eff)
        ConnectF con ->
          case fdecompIdx n con of
            Right (a, rest) -> getNode $ loop (comb z a) rest
            Left other -> ConnectF (fmap (loop z) other)

foldMOn ::
     (Functor m, IWithout n cs cs', All Functor cs')
  => (x -> a -> m x)
  -> m x
  -> (x -> m b)
  -> IIndex n cs (Yielding a)
  -> Node cs m r
  -> Node cs' m (b, r)
foldMOn comb seed fin n node' = Node (EffectF (fmap (flip loop node') seed))
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

foldOnly ::
     Monad m => (x -> a -> x) -> x -> (x -> b) -> Producer a m r -> m (b, r)
foldOnly comb seed fin = run . foldOn comb seed fin i0

foldMOnly ::
     Monad m
  => (x -> a -> m x)
  -> m x
  -> (x -> m b)
  -> Producer a m r
  -> m (b, r)
foldMOnly comb seed fin = run . foldMOn comb seed fin i0
