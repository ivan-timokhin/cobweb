{-|
Module: Cobweb.Internal
Description: Exposes internal workings of Node
Copyright: 2017 © Ivan Timokhin
License: BSD3
Maintainer: timokhin.iv@gmail.com
Stability: experimental

Underneath, 'Node' is a free monad over sum of @m@ and all of
communication functors.

This has important implication in that 'Node' violates monad
transformer laws.  Both of them, actually:

  [@'lift' . 'return' = 'return'@] is violated because the former has
  an 'EffectF' layer on top, while the latter is purely 'ReturnF';

  [@'lift' (m '>>=' f) = 'lift' m '>>=' ('lift' . f)@] is violated
  because the former will have one 'EffectF' layer, while the latter
  two.

Neither of these should be visible without importing this module so
any visible violation of monad transformer laws is still a bug in the
library.  However, this structural violation means that data types and
functions defined in this module should be handled with care, as they
are potentially unsafe.

The motivation for said design primarily stems from the desire to
avoid ‘dropping’ into the base monad at every step, even when we're
simply trying to pass around some values through communication
channels, with no effects from the base monad required.
-}
{-# OPTIONS_HADDOCK show-extensions #-}
{-# LANGUAGE BangPatterns #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE UndecidableInstances #-}

module Cobweb.Internal
  ( Node(Return, Connect, Effect)
  , cata
  , unsafeHoist
  , transformCons
  , inspect
  , unfold
  , observe
  ) where

import Control.Monad (ap, liftM)
import Control.Monad.Base (MonadBase(liftBase))
import Control.Monad.Catch (MonadCatch(catch), MonadThrow(throwM))
import Control.Monad.Except (MonadError(catchError, throwError))
import qualified Control.Monad.Fail as Fail
import Control.Monad.IO.Class (MonadIO(liftIO))
import Control.Monad.Morph (MFunctor(hoist), MMonad(embed))
import Control.Monad.Primitive (PrimMonad(PrimState, primitive))
import Control.Monad.Reader.Class (MonadReader(ask, local, reader))
import Control.Monad.RWS.Class (MonadRWS)
import Control.Monad.State.Class (MonadState(get, put, state))
import Control.Monad.Trans (MonadTrans(lift))
import Control.Monad.Trans.Resource (MonadResource(liftResourceT))
import Control.Monad.Writer.Class
       (MonadWriter(listen, pass, tell, writer), censor)

import Cobweb.Type.Combinators (All, FSum, Inductive)

-- | A monad transformer that extends the underlying monad @m@ with a
-- capacity to communicate on a list of channels @cs@.
--
-- Channels are 'Functor's, values of which can be embedded into the
-- computation.  For example,
--
-- @
-- 'Node' '[(,) a, (->) b, (,) c] m r
-- @
--
-- produces values of type @a@ on the first channel, consumes values
-- of type @b@ on the second, and produces values of type @c@ on the
-- third.  "Cobweb.Core" provides aliases for these (most common)
-- channel types: 'Cobweb.Core.Yield' for @(,)@, and
-- 'Cobweb.Core.Await' for @(->)@.
data Node cs m r
  = Return r -- ^ The computation has completed, producing resulting value.
  | Effect (m (Node cs m r)) -- ^ Invoke effect in the base monad.
  | Connect (FSum cs (Node cs m r)) -- ^ Initiate communcation on one
                                    -- of the channels.

-- | Fold a 'Node'
cata ::
     (All Functor cs, Inductive cs, Functor m)
  => (r -> a)
  -> (FSum cs a -> a)
  -> (m a -> a)
  -> Node cs m r
  -> a
{-# INLINE cata #-}
cata algR algC algE = loop
  where
    loop (Return r) = algR r
    loop (Connect con) = algC (fmap loop con)
    loop (Effect eff) = algE (fmap loop eff)

instance (All Functor cs, Inductive cs, Functor m) => Functor (Node cs m) where
  fmap = liftM

instance (All Functor cs, Inductive cs, Functor m) =>
         Applicative (Node cs m) where
  pure = Return
  (<*>) = ap
  (*>) = (>>)

instance (All Functor cs, Inductive cs, Functor m) => Monad (Node cs m) where
  (>>=) = bind_

bind_ ::
     (All Functor cs, Inductive cs, Functor m)
  => Node cs m a
  -> (a -> Node cs m b)
  -> Node cs m b
{-# INLINE[0] bind_ #-}
bind_ x f = cata f Connect Effect x

{-# RULES
"cobweb/bind_/return" forall a f . bind_ (Return a) f = f a
"cobweb/bind_/connect" forall con f.
  bind_ (Connect con) f = Connect (fmap (`bind_` f) con)
"cobweb/bind_/effect" forall eff f.
  bind_ (Effect eff) f = Effect (fmap (`bind_` f) eff)
 #-}

instance MonadTrans (Node cs) where
  lift eff = Effect $ fmap Return eff

instance (All Functor cs, Inductive cs, MonadIO m) => MonadIO (Node cs m) where
  liftIO = lift . liftIO

instance (All Functor cs, Inductive cs, Fail.MonadFail m) =>
         Fail.MonadFail (Node cs m) where
  fail = lift . Fail.fail

-- | Lift a @catch@-like function from the base level to 'Node'.
liftCatch ::
     (All Functor cs, Inductive cs, Applicative m)
  => (m (Node cs m a) -> (e -> m (Node cs m a)) -> m (Node cs m a))
  -> Node cs m a
  -> (e -> Node cs m a)
  -> Node cs m a
liftCatch catchBase node handler =
  cata Return Connect (\eff -> Effect $ eff `catchBase` (pure . handler)) node

instance (All Functor cs, Inductive cs, MonadError e m) =>
         MonadError e (Node cs m) where
  throwError = lift . throwError
  catchError = liftCatch catchError

-- | This instance is safe only if @'local' f@ in the base monad is a
-- proper monad morphism (see "Control.Monad.Morph" for details),
-- which it usually is.
instance (All Functor cs, Inductive cs, MonadReader r m) =>
         MonadReader r (Node cs m) where
  ask = lift ask
  reader = lift . reader
  -- This relies on `local f` being proper monad morphism… which is
  -- unknowable, since mtl doesn't have any laws on its
  -- classes. *grumble*
  local f = unsafeHoist (local f)

-- | Both 'listen' and 'pass' accumulate intermediate results
-- strictly.
instance (All Functor cs, Inductive cs, MonadWriter w m) =>
         MonadWriter w (Node cs m) where
  writer = lift . writer
  tell = lift . tell
  listen = loop mempty
    where
      loop !m (Return r) = Return (r, m)
      loop !m (Connect con) = Connect (fmap (loop m) con)
      loop !m (Effect eff) =
        Effect $ do
          (x, w) <- listen eff
          pure (loop (m `mappend` w) x)
  pass = loop mempty
    where
      loop !m (Return (r, f)) =
        Effect $ do
          tell (f m)
          pure (pure r)
      loop !m (Connect con) = Connect (fmap (loop m) con)
      loop !m (Effect eff) =
        Effect $ do
          (x, w) <- censor (const mempty) (listen eff)
          pure (loop (m `mappend` w) x)

instance (All Functor cs, Inductive cs, MonadState s m) =>
         MonadState s (Node cs m) where
  get = lift get
  put = lift . put
  state = lift . state

instance (All Functor cs, Inductive cs, MonadRWS r w s m) =>
         MonadRWS r w s (Node cs m)

instance (All Functor cs, Inductive cs, MonadBase b m) =>
         MonadBase b (Node cs m) where
  liftBase = lift . liftBase

instance (All Functor cs, Inductive cs, MonadThrow m) =>
         MonadThrow (Node cs m) where
  throwM = lift . throwM

instance (All Functor cs, Inductive cs, MonadCatch m) =>
         MonadCatch (Node cs m) where
  catch = liftCatch catch

instance (All Functor cs, Inductive cs, MonadResource m) =>
         MonadResource (Node cs m) where
  liftResourceT = lift . liftResourceT

instance (All Functor cs, Inductive cs, PrimMonad m) =>
         PrimMonad (Node cs m) where
  type PrimState (Node cs m) = PrimState m
  primitive = lift . primitive

instance (All Functor cs, Inductive cs) => MFunctor (Node cs) where
  hoist f = unsafeHoist f . observe

instance (All Functor cs, Inductive cs) => MMonad (Node cs) where
  embed f = loop
    where
      loop (Return r) = Return r
      loop (Connect con) = Connect (fmap loop con)
      loop (Effect eff) = f eff >>= loop

-- | Same as 'hoist', but potentially unsafe when the function passed
-- is /not/ a proper monad morphism.
--
-- The problem is that, as mentioned on the top of the module, 'Node'
-- violates monad transformer laws, and while said violations should
-- make no visible difference for a proper monad morphism, a general
-- monad transformation /can/ notice it (e.g. by counting the number
-- of the times it is called).
--
-- This problem is avoided in 'MFunctor' instance of 'Node' by
-- transforming 'Node' in a ‘canonical’ form via 'observe' prior to
-- passing it to 'unsafeHoist'; this restores the monad transformer
-- laws, but incurs a performance penalty.
unsafeHoist ::
     (All Functor cs, Inductive cs, Functor m)
  => (forall x. m x -> n x)
  -> Node cs m r
  -> Node cs n r
unsafeHoist f = cata Return Connect (Effect . f)

-- | Transform a full communication stack of a 'Node'.
--
-- Due to type-specialised nature of the transformation function, this
-- function is more flexible (but also less safe!) than the similar
-- 'Cobweb.Core.gmapAll'.
transformCons ::
     (Functor m, Inductive cs, All Functor cs)
  => (FSum cs (Node cs' m r) -> FSum cs' (Node cs' m r))
     -- ^ Transform each communication request.
  -> Node cs m r
  -> Node cs' m r
transformCons f = cata Return (Connect . f) Effect

-- | Run the 'Node' until it either completes, or initiates
-- communication on one of its channels.
inspect :: Monad m => Node cs m r -> m (Either r (FSum cs (Node cs m r)))
inspect node =
  case node of
    Return r -> pure (Left r)
    Effect eff -> eff >>= inspect
    Connect con -> pure (Right con)

-- | Build a 'Node' by unfolding from a seed.
unfold ::
     (Functor m, Inductive cs, All Functor cs)
  => (b -> m (Either r (FSum cs b))) -- ^ Step function; return value
     -- of 'Left' implies termination, while 'Right' implies
     -- communication request.
  -> b -- ^ Initial seed.
  -> Node cs m r
unfold step = loop
  where
    loop seed = Effect (fmap loopstep (step seed))
    loopstep (Left r) = Return r
    loopstep (Right con) = Connect (fmap loop con)

-- | Transform 'Node' to a ‘canonical’ form, where monad transformer
-- laws hold structurally.
--
-- The ‘canonical’ form begins with and 'EffectF' layer, then
-- 'ConnectF' layers interleaved with 'EffectF' layers until, after
-- the final 'EffectF', comes 'ReturnF'.  This involves complete
-- reconstruction of the 'Node', and requires ‘dropping’ into the base
-- monad at every sneeze, so should not be done lightheartedly.
--
-- @
-- 'observe' = 'unfold' 'inspect'
-- @
observe :: (Monad m, All Functor cs, Inductive cs) => Node cs m r -> Node cs m r
observe = unfold inspect
