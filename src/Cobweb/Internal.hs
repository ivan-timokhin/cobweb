{-|
Module: Cobweb.Internal
Description: Exposes internal workings of Node
Copyright: 2017 © Ivan Timokhin
License: BSD3
Maintainer: timokhin.iv@gmail.com
Stability: experimental

Underneath, 'Node' is

  * a free monad over sum of @m@ and all of communication functors,
    and

  * a fixed point of 'NodeF' functor.

The first point has important implication in that 'Node' violates
monad transformer laws.  Both of them, actually:

  [@'lift' . 'return' = 'return'@] is violated because the former has
  an 'EffectF' layer on top, while the latter is purely 'ReturnF';

  [@'lift' (m '>>=' f) = 'lift' m '>>=' ('lift' . f)@] is violated
  because the former will have one 'EffectF' layer, while the latter
  two.

Neither of these should be visible without importing this module or
using 'Recursive' instance of 'Node' (which requires 'NodeF' to be
used productively anyway), so any visible violation of monad
transformer laws is still a bug in the library.  However, this
structural violation means that data types and functions defined in
this module should be handled with care, as they are potentially
unsafe.

The motivation for said design primarily stems from the desire to
avoid ‘dropping’ into the base monad at every step, even when we're
simply trying to pass around some values through communication
channels, with no effects from the base monad required.
-}
{-# OPTIONS_HADDOCK show-extensions #-}
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
import Control.Monad.Base (MonadBase(liftBase))
import Control.Monad.Catch (MonadCatch(catch), MonadThrow(throwM))
import Control.Monad.Except (MonadError(catchError, throwError))
import qualified Control.Monad.Fail as Fail
import Control.Monad.IO.Class (MonadIO(liftIO))
import Control.Monad.Morph (MFunctor(hoist), MMonad(embed))
import Control.Monad.Primitive (PrimMonad(PrimState, primitive))
import Control.Monad.Reader.Class (MonadReader(ask, local, reader))
import Control.Monad.State.Class (MonadState(get, put, state))
import Control.Monad.Trans (MonadTrans(lift))
import Control.Monad.Trans.Resource (MonadResource(liftResourceT))
import Data.Bifunctor (Bifunctor(first, second))
import Data.Functor.Foldable (Base, Recursive(cata, project))
import Data.Type.Sum.Lifted (FSum)

import Cobweb.Type.Combinators (All)

-- | The base functor of 'Node'.
data NodeF (cs :: [* -> *]) (m :: * -> *) r a
  = ReturnF r -- ^ The computation has completed, producing resulting value.
  | EffectF (m a) -- ^ Invoke effect in the base monad.
  | ConnectF (FSum cs a) -- ^ Initiate communcation on one of the channels.

deriving instance
         (All Functor cs, Functor m) => Functor (NodeF cs m r)

instance (All Functor cs, Functor m) => Bifunctor (NodeF cs m) where
  first f (ReturnF r) = ReturnF (f r)
  first _ (EffectF eff) = EffectF eff
  first _ (ConnectF con) = ConnectF con
  second = fmap

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
-- channel types: 'Cobweb.Core.Yielding' for @(,)@, and
-- 'Cobweb.Core.Awaiting' for @(->)@.
newtype Node cs m r = Node
  { getNode :: NodeF cs m r (Node cs m r)
  }

type instance Base (Node cs m r) = NodeF cs m r

instance (All Functor cs, Functor m) => Recursive (Node cs m r) where
  project = getNode

-- | Convert 'Node' from one set of parameters to another, one level
-- at a time.
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

-- | Lift a @catch@-like function from the base level to 'Node'.
liftCatch ::
     (All Functor cs, Applicative m)
  => (m (Node cs m a) -> (e -> m (Node cs m a)) -> m (Node cs m a))
  -> Node cs m a
  -> (e -> Node cs m a)
  -> Node cs m a
liftCatch catchBase node handler = transform alg node
  where
    alg (ReturnF r) = ReturnF r
    alg (ConnectF con) = ConnectF con
    alg (EffectF eff) = EffectF $ eff `catchBase` (pure . handler)

instance (All Functor cs, MonadError e m) => MonadError e (Node cs m) where
  throwError = lift . throwError
  catchError = liftCatch catchError

-- | This instance is safe only if @'local' f@ in the base monad is a
-- proper monad morphism (see "Control.Monad.Morph" for details),
-- which it usually is.
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

instance (All Functor cs, MonadBase b m) => MonadBase b (Node cs m) where
  liftBase = lift . liftBase

instance (All Functor cs, MonadThrow m) => MonadThrow (Node cs m) where
  throwM = lift . throwM

instance (All Functor cs, MonadCatch m) => MonadCatch (Node cs m) where
  catch = liftCatch catch

instance (All Functor cs, MonadResource m) => MonadResource (Node cs m) where
  liftResourceT = lift . liftResourceT

instance (All Functor cs, PrimMonad m) => PrimMonad (Node cs m) where
  type PrimState (Node cs m) = PrimState m
  primitive = lift . primitive

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
     (All Functor cs, Functor m)
  => (forall x. m x -> n x)
  -> Node cs m r
  -> Node cs n r
unsafeHoist f = transform alg
  where
    alg (ReturnF r) = ReturnF r
    alg (ConnectF con) = ConnectF con
    alg (EffectF eff) = EffectF (f eff)

-- | Run the 'Node' until it either completes, or initiates
-- communication on one of its channels.
inspect :: Monad m => Node cs m r -> m (Either r (FSum cs (Node cs m r)))
inspect (Node web) =
  case web of
    ReturnF r -> pure (Left r)
    EffectF eff -> eff >>= inspect
    ConnectF con -> pure (Right con)

-- | Build a 'Node' by unfolding from a seed.
unfold ::
     (Functor m, All Functor cs)
  => (b -> m (Either r (FSum cs b))) -- ^ Step function; return value
     -- of 'Left' implies termination, while 'Right' implies
     -- communication request.
  -> b -- ^ Initial seed.
  -> Node cs m r
unfold step = loop
  where
    loop seed = Node (EffectF (fmap (Node . loopstep) (step seed)))
    loopstep (Left r) = ReturnF r
    loopstep (Right con) = ConnectF (fmap loop con)

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
observe :: (Monad m, All Functor cs) => Node cs m r -> Node cs m r
observe = unfold inspect
