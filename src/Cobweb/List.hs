{-|
Module: Cobweb.List
Description: @ListT@ done right.
Copyright: 2017 © Ivan Timokhin
License: BSD3
Maintainer: timokhin.iv@gmail.com
Stability: experimental

This module provides a 'ListT' monad transformer, which extends the
base monad with 'Alternative'/'MonadPlus' instances of ‘choose both’
variety.  That is, if there's something like

> choice <- pure True <|> pure False


in the @do@-block, the rest of the computation will get executed
/twice/, once with @choice@ bound to 'True', and once with it bound to
'False'.

Note that this is implemented by nesting loops ('>>=' for 'ListT' is
just 'for'), so the control flow is slightly unusual.  In the above
example, /the entire rest of the computation/ will run first in the
'True' branch, and then run /again/ in the 'False' branch.  This means
that any modifications to the monadic state, including throwing
exceptions, that occur in the first branch are visible in the second,
even if they come later lexically.
-}
{-# OPTIONS_HADDOCK show-extensions #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE UndecidableInstances #-}

module Cobweb.List
  ( ListT(ListT, runListT)
  ) where

import Control.Applicative (Alternative((<|>), empty))
import Control.Monad (MonadPlus, ap)
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
import Data.Semigroup (Semigroup((<>)))

import Cobweb.Core (connect, i0, mapOn)
import Cobweb.Internal (cata)
import Cobweb.Producer (Producer, for, yield)

-- | A monad transformer that adds ‘choose both’-style 'Alternative'
-- instance to the underlying monad.
newtype ListT m a = ListT
  { runListT :: Producer a m ()
  }

instance Functor (ListT m) where
  fmap f = ListT . mapOn i0 f . runListT

instance Applicative (ListT m) where
  pure = ListT . yield
  (<*>) = ap

instance Monad (ListT m) where
  x >>= f = ListT $ for (runListT x) (runListT . f)

instance Semigroup (ListT m a) where
  x <> y = ListT $ runListT x >> runListT y

instance Monoid (ListT m a) where
  mempty = ListT (pure ())
  mappend = (<>)

instance Alternative (ListT m) where
  empty = mempty
  (<|>) = mappend

instance MonadPlus (ListT m)

instance MonadTrans ListT where
  lift x =
    ListT $ do
      x' <- lift x
      yield x'

instance MFunctor ListT where
  hoist f = ListT . hoist f . runListT

instance MonadIO m => MonadIO (ListT m) where
  liftIO = lift . liftIO

instance Fail.MonadFail m => Fail.MonadFail (ListT m) where
  fail = lift . Fail.fail

-- TODO figure out if/how this works
instance MonadError e m => MonadError e (ListT m) where
  throwError = ListT . throwError
  x `catchError` handler = ListT $ runListT x `catchError` (runListT . handler)

instance MonadReader r m => MonadReader r (ListT m) where
  ask = lift ask
  reader = lift . reader
  local f = ListT . local f . runListT

instance MonadState s m => MonadState s (ListT m) where
  get = lift get
  put = lift . put
  state = lift . state

instance MonadBase b m => MonadBase b (ListT m) where
  liftBase = lift . liftBase

instance MonadThrow m => MonadThrow (ListT m) where
  throwM = lift . throwM

instance MonadCatch m => MonadCatch (ListT m) where
  x `catch` handler = ListT $ runListT x `catch` (runListT . handler)

instance PrimMonad m => PrimMonad (ListT m) where
  type PrimState (ListT m) = PrimState m
  primitive = lift . primitive

instance MonadResource m => MonadResource (ListT m) where
  liftResourceT = lift . liftResourceT

instance MMonad ListT where
  embed f (ListT node) =
    ListT $
    cata
      pure
      (\c cont -> connect c >>= cont)
      (\eff cont -> for (runListT $ f eff) cont)
      node
