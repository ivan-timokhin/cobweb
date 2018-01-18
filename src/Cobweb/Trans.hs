{-|
Module: Cobweb.Trans
Description: Interoperability with other transformers.
Copyright: 2017 © Ivan Timokhin
License: BSD3
Maintainer: timokhin.iv@gmail.com
Stability: experimental

-}
{-# OPTIONS_HADDOCK show-extensions #-}
module Cobweb.Trans
  ( distribute
    -- * State
    -- ** Strict
  , runStateN
  , evalStateN
  , execStateN
    -- ** Lazy
  , runLazyStateN
  , evalLazyStateN
  , execLazyStateN
    -- * Reader
  , runReaderN
    -- * Except
  , runExceptN
    -- * Writer
    -- ** Strict
  , runWriterN
  , execWriterN
    -- ** Lazy
  , runLazyWriterN
  , execLazyWriterN
  ) where

import Control.Monad.Morph (MFunctor(hoist))
import Control.Monad.Trans (MonadTrans(lift))
import qualified Control.Monad.State.Lazy as SL
import qualified Control.Monad.State.Strict as SS
import qualified Control.Monad.Reader as R
import qualified Control.Monad.Except as E
import qualified Control.Monad.Writer.Strict as WS
import qualified Control.Monad.Writer.Lazy as WL

import Cobweb.Core (Node, connect, gforAll, run)
import Cobweb.Internal (build, cata)

-- | Move a single transformer layer from ‘beneath’ the 'Node' to
-- ‘above’ it.
--
-- This is the central function of the module; other functions
-- provided here merely wrap compose 'distribute' with corresponding
-- transformer-specific functions.
distribute ::
     (Monad m, MonadTrans t, MFunctor t, Monad (t m), Monad (t (Node cs m)))
  => Node cs (t m) a -- ^ A 'Node' above a transformer layer.
  -> t (Node cs m) a -- ^ Same 'Node' beneath a transformer layer.
distribute node
  -- Here's an explanation:
  --
  -- First, we insert a fresh 'Node' layer beneath @t@
  -- (so Node (t m) --> Node (t (Node m))).  This is the hoisting part.
  --
  -- Second, we iterate over old connections via 'gforAll', and move
  -- them all to the new 'Node' layer.  This is the lift.lift part.
  --
  -- Finally, now that the outer layer has no outstanding connections,
  -- we simply run it.
 = run $ gforAll (hoist (hoist lift) node) (lift . lift . connect)

-- | Run 'SS.StateT', returning both final state and result.
runStateN :: Monad m => Node cs (SS.StateT s m) a -> s -> Node cs m (a, s)
runStateN = SS.runStateT . distribute

-- | Run 'SS.StateT', returning only the result.
evalStateN :: Monad m => Node cs (SS.StateT s m) a -> s -> Node cs m a
evalStateN = SS.evalStateT . distribute

-- | Run 'SS.StateT', returning only the final state.
execStateN :: Monad m => Node cs (SS.StateT s m) a -> s -> Node cs m s
execStateN = SS.execStateT . distribute

-- | Run 'SL.StateT', returning both final state and result.
runLazyStateN :: Monad m => Node cs (SL.StateT s m) a -> s -> Node cs m (a, s)
runLazyStateN = SL.runStateT . distribute

-- | Run 'SL.StateT', returning only the result.
evalLazyStateN :: Monad m => Node cs (SL.StateT s m) a -> s -> Node cs m a
evalLazyStateN = SL.evalStateT . distribute

-- | Run 'SL.StateT', returning only the final state.
execLazyStateN :: Monad m => Node cs (SL.StateT s m) a -> s -> Node cs m s
execLazyStateN = SL.execStateT . distribute

-- | Run 'R.ReaderT' underneath the 'Node'
runReaderN :: Monad m => Node cs (R.ReaderT r m) a -> r -> Node cs m a
runReaderN = R.runReaderT . distribute

-- | Run 'E.ExceptT', returning either the error, or the result.
runExceptN :: Monad m => Node cs (E.ExceptT e m) a -> Node cs m (Either e a)
runExceptN = E.runExceptT . distribute

-- | Run 'WS.WriterT', returning both the value and the output.
runWriterN :: Monoid w => Node cs (WS.WriterT w m) a -> Node cs m (a, w)
runWriterN node =
  build
    (\ret con lft ->
       cata
         (curry ret)
         (\c cont w -> con c (`cont` w))
         (\e cont w ->
            lft (WS.runWriterT e) (\(x, w') -> cont x (w `mappend` w')))
         node
         mempty)

-- | Run 'WS.WriterT', returning only the output.
execWriterN :: Monoid w => Node cs (WS.WriterT w m) a -> Node cs m w
execWriterN = fmap snd . runWriterN

-- | Run 'WL.WriterT', returning both the value and the output.
runLazyWriterN :: Monoid w => Node cs (WL.WriterT w m) a -> Node cs m (a, w)
runLazyWriterN node =
  build
    (\ret con lft ->
       cata
         (curry ret)
         (\c cont w -> con c (`cont` w))
         (\e cont w ->
            lft (WL.runWriterT e) (\ ~(x, w') -> cont x (w `mappend` w')))
         node
         mempty)

-- | Run 'WL.WriterT', returning both the value and the output.
execLazyWriterN :: Monoid w => Node cs (WL.WriterT w m) a -> Node cs m w
execLazyWriterN = fmap snd . runLazyWriterN
