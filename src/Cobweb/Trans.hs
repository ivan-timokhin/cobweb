{-# LANGUAGE ScopedTypeVariables #-}

module Cobweb.Trans where

import Control.Monad (join)
import Control.Monad.Morph (MFunctor(hoist))
import Control.Monad.Trans (MonadTrans(lift))

import Cobweb.Core (connects)
import Cobweb.Internal
       (Node, NodeF(ConnectF, EffectF, ReturnF), cata)
import Cobweb.Type.Combinators (All)

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
    -- What happens here is that we're trying to interpret our
    -- existing stack in a new monad.  Joins are essentially plumbing;
    -- compare with 'run'; the way 'cata' works, we essentially
    -- convert layer-by-layer, starting from the bottom.  So when we
    -- convert the next layer, we smash it together with what is
    -- already done underneath it via 'join'.
    alg :: NodeF cs (t m) r (t (Node cs m) r) -> t (Node cs m) r
    -- Pure values are easy.
    alg (ReturnF r) = pure r
    -- We have an effect in (t m), and want an effect in
    -- (t (Node cs m)).  We essentially want to insert another
    -- transformer layer right beneath @t@, which is /exactly/ what
    -- 'hoist' was created for.
    alg (EffectF eff) = join $ hoist lift eff
    -- We need to make the same connection in t (Node cs m).  That is
    -- easy; we just use 'connects' to get @Node cs m@ (because
    -- 'connects' is polymorphic in the base monad), and then lift it
    -- to @t (Node cs m)@.
    alg (ConnectF con) = join $ lift (connects con)
