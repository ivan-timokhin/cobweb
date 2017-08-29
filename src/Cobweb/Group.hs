{-# LANGUAGE DataKinds #-}

module Cobweb.Group where

import Cobweb.Internal
       (Node(Node, getNode), NodeF(ConnectF, EffectF, ReturnF))
import Cobweb.Type.Combinators (finjectIdx, i0)

chunkBy ::
     (Functor c, Functor m)
  => Int
  -> Node '[ c] m r
  -> Node '[ Node '[ c] m] m r
chunkBy n = loop
  where
    loop node =
      Node $
      case getNode node of
        ReturnF r -> ReturnF r
        EffectF eff -> EffectF (fmap loop eff)
        ConnectF _ -> ConnectF (finjectIdx i0 $ chunkOff n node)
    chunkOff m node
      | m <= 0 = pure (loop node)
      | otherwise =
        Node $
        case getNode node of
          ReturnF r -> ReturnF (pure r)
          EffectF eff -> EffectF (fmap (chunkOff m) eff)
          ConnectF con -> ConnectF (fmap (chunkOff (m - 1)) con)
