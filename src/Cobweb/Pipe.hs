{-|
Module: Cobweb.Pipes
Description: Nodes that yield and await values.
Copyright: 2017 © Ivan Timokhin
License: BSD3
Maintainer: timokhin.iv@gmail.com
Stability: experimental

Nodes yield and await values.

-}
{-# OPTIONS_HADDOCK show-extensions #-}
{-# LANGUAGE DataKinds #-}

module Cobweb.Pipe
  ( Pipe
  , await
  , yield
    -- * Special pipes
  , cat
  , mapping
  , mappingM
  , taking
  , dropping
  ) where

import Control.Monad (forever, replicateM_)
import Control.Monad.Trans (lift)

import Cobweb.Consumer (await)
import Cobweb.Core (Pipe)
import Cobweb.Producer (yield)

-- | Identity pipe, simply forwards the values received to the output
-- channel.
cat :: Pipe a a m r
cat =
  forever $ do
    x <- await
    yield x

-- | Apply a function to all values passing through.
mapping :: (a -> b) -> Pipe a b m r
{-# INLINE mapping #-}
mapping f =
  forever $ do
    a <- await
    yield (f a)

-- | Apply a function with possible side effects to all values passing
-- through.
mappingM :: Monad m => (a -> m b) -> Pipe a b m r
mappingM f =
  forever $ do
    a <- await
    b <- lift (f a)
    yield b

-- | Let through a specified number of values, then terminate.
taking :: Int -> Pipe a a m ()
taking n = replicateM_ n $ await >>= yield

-- | Skip a specified number of values, forward the rest.
dropping :: Int -> Pipe a a m ()
dropping n = do
  replicateM_ n await
  cat
