{-# LANGUAGE DeriveFunctor #-}
{-# LANGUAGE UndecidableInstances #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE StandaloneDeriving #-}
{-# LANGUAGE KindSignatures #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE RankNTypes #-}

module Cobweb.Internal
  ( NodeF(ReturnF, EffectF, ConnectF)
  , Node(Node, getNode)
  , transform
  , unsafeHoist
  , inspect
  , unfold
  , observe
  ) where

import Control.Monad (ap)
import qualified Control.Monad.Fail as Fail
import Control.Monad.IO.Class (MonadIO(liftIO))
import Control.Monad.Morph (MFunctor(hoist))
import Control.Monad.Trans (MonadTrans(lift))
import Data.Functor.Foldable (Base, Recursive(cata, project))
import Data.Type.Sum.Lifted (FSum)

import Cobweb.Type.Combinators (All)

data NodeF (cs :: [* -> *]) (m :: * -> *) r a
  = ReturnF r
  | EffectF (m a)
  | ConnectF (FSum cs a)

deriving instance
         (All Functor cs, Functor m) => Functor (NodeF cs m r)

newtype Node cs m r = Node
  { getNode :: NodeF cs m r (Node cs m r)
  }

type instance Base (Node cs m r) = NodeF cs m r

instance (All Functor cs, Functor m) => Recursive (Node cs m r) where
  project = getNode

transform ::
     (All Functor cs, Functor m)
  => (NodeF cs m r (Node cs' m' r') -> NodeF cs' m' r' (Node cs' m' r'))
  -> Node cs m r
  -> Node cs' m' r'
transform alg = cata (Node . alg)

instance (All Functor cs, Functor m) => Functor (Node cs m) where
  fmap f = transform alg
    where
      alg (ReturnF r) = ReturnF (f r)
      alg (EffectF eff) = EffectF eff
      alg (ConnectF con) = ConnectF con

instance (All Functor cs, Functor m) => Applicative (Node cs m) where
  pure = Node . ReturnF
  (<*>) = ap

instance (All Functor cs, Functor m) => Monad (Node cs m) where
  x >>= f = transform alg x
    where
      alg (ReturnF r) = getNode (f r)
      alg (EffectF eff) = EffectF eff
      alg (ConnectF con) = ConnectF con

instance MonadTrans (Node cs) where
  lift eff = Node $ EffectF $ fmap (Node . ReturnF) eff

instance (All Functor cs, MonadIO m) => MonadIO (Node cs m) where
  liftIO = lift . liftIO

instance (All Functor cs, Fail.MonadFail m) => Fail.MonadFail (Node cs m) where
  fail = lift . Fail.fail

-- This instance is "undecidable", but it's fine, since HSum doesn't
-- actually know anything about Node, and expands in functor
-- instances for each interface in the list.
instance All Functor cs => MFunctor (Node cs) where
  hoist f = unsafeHoist f . observe

unsafeHoist ::
     (All Functor cs, Functor m)
  => (forall x. m x -> n x)
  -> Node cs m r
  -> Node cs n r
unsafeHoist f = transform alg
  where
    alg (ReturnF r) = ReturnF r
    alg (ConnectF con) = ConnectF con
    alg (EffectF eff) = EffectF (f eff)

inspect :: Monad m => Node cs m r -> m (Either r (FSum cs (Node cs m r)))
inspect (Node web) =
  case web of
    ReturnF r -> pure (Left r)
    EffectF eff -> eff >>= inspect
    ConnectF con -> pure (Right con)

unfold ::
     (Functor m, All Functor cs)
  => (b -> m (Either r (FSum cs b)))
  -> b
  -> Node cs m r
unfold step = loop
  where
    loop seed = Node (EffectF (fmap (Node . loopstep) (step seed)))
    loopstep (Left r) = ReturnF r
    loopstep (Right con) = ConnectF (fmap loop con)

observe :: (Monad m, All Functor cs) => Node cs m r -> Node cs m r
observe = unfold inspect
