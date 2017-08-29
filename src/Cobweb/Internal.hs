{-# LANGUAGE DataKinds #-}
{-# LANGUAGE DeriveFunctor #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE KindSignatures #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE StandaloneDeriving #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE UndecidableInstances #-}

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
import Control.Monad.Except (MonadError(catchError, throwError))
import qualified Control.Monad.Fail as Fail
import Control.Monad.IO.Class (MonadIO(liftIO))
import Control.Monad.Morph (MFunctor(hoist), MMonad(embed))
import Control.Monad.Reader.Class (MonadReader(ask, local, reader))
import Control.Monad.State.Class (MonadState(get, put, state))
import Control.Monad.Trans (MonadTrans(lift))
import Data.Bifunctor (Bifunctor(first, second))
import Data.Functor.Foldable (Base, Recursive(cata, project))
import Data.Type.Sum.Lifted (FSum)

import Cobweb.Type.Combinators (All)

data NodeF (cs :: [* -> *]) (m :: * -> *) r a
  = ReturnF r
  | EffectF (m a)
  | ConnectF (FSum cs a)

deriving instance
         (All Functor cs, Functor m) => Functor (NodeF cs m r)

instance (All Functor cs, Functor m) => Bifunctor (NodeF cs m) where
  first f (ReturnF r) = ReturnF (f r)
  first _ (EffectF eff) = EffectF eff
  first _ (ConnectF con) = ConnectF con
  second = fmap

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
  fmap f = transform (first f)

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

instance (All Functor cs, MonadError e m) => MonadError e (Node cs m) where
  throwError = lift . throwError
  catchError node handler = loop node
    where
      loop n =
        Node $
        case getNode n of
          ReturnF r -> ReturnF r
          ConnectF con -> ConnectF (fmap loop con)
          EffectF eff -> EffectF $ fmap loop eff `catchError` (pure . handler)

instance (All Functor cs, MonadReader r m) => MonadReader r (Node cs m) where
  ask = lift ask
  reader = lift . reader
  -- This relies on `local f` being proper monad morphism… which is
  -- unknowable, since mtl doesn't have any laws on its
  -- classes. *grumble*
  local f = unsafeHoist (local f)

-- MonadWrite is absent primarily because of listen; the problem is
-- that, since we have an entire list of monadic actions, it is
-- necessary to listen on each individually, and then manually combine
-- the results.  That wouldn't be too bad, but there are two ways to
-- do that—strict and lazy—and while the usual preference is to be as
-- strict as possible, I just know there's someone out there who
-- relies on this laziness for some clever recursive-knot-tying, and
-- whose code will be irreparably broken by introducing strict operations.
--
-- The moral of the story is that if it is impossible to do correctly,
-- I'd rather not do it at all.
instance (All Functor cs, MonadState s m) => MonadState s (Node cs m) where
  get = lift get
  put = lift . put
  state = lift . state

instance All Functor cs => MFunctor (Node cs) where
  hoist f = unsafeHoist f . observe

instance All Functor cs => MMonad (Node cs) where
  embed f = loop
    where
      loop node =
        Node $
        case getNode node of
          ReturnF r -> ReturnF r
          ConnectF con -> ConnectF (fmap loop con)
          EffectF eff -> getNode $ f eff >>= loop

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
