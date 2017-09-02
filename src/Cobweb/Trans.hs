{-# LANGUAGE ScopedTypeVariables #-}

module Cobweb.Trans where

import Control.Monad (join)
import Control.Monad.Morph (MFunctor(hoist))
import Control.Monad.Trans (MonadTrans(lift))

import Cobweb.Core (connects)
import Cobweb.Internal
       (Node, NodeF(ConnectF, EffectF, ReturnF), cata)
import Cobweb.Type.Combinators (All)

-- FIXME figure out what it does and, depending on results,
-- a) rewrite it correctly;
-- b) rewrite it in a more understandable fashion, if it turns out to
-- be correct;
-- c) if none of the above applies/helps, at least explain what
-- happens here in comments.
distribute ::
     forall m t cs r.
     ( Monad m
     , MonadTrans t
     , MFunctor t
     , Monad (t m)
     , Monad (t (Node cs m))
     , All Functor cs
     )
  => Node cs (t m) r
  -> t (Node cs m) r
distribute = cata alg
  where
    alg :: NodeF cs (t m) r (t (Node cs m) r) -> t (Node cs m) r
    alg (ReturnF r) = pure r
    alg (EffectF eff) = join $ hoist lift eff
    alg (ConnectF con) = join $ lift $ connects con
