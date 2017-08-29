{-# LANGUAGE DataKinds #-}
module Cobweb where

import Control.Monad (forever)
import Control.Monad.IO.Class (MonadIO(liftIO))

import Cobweb.Consumer (Consumer)
import Cobweb.Core (awaitOn, yieldOn)
import Cobweb.Internal (Node)
import Cobweb.Producer (Producer)
import Cobweb.Type.Combinators (i0)

onlyOne :: Node '[ c] m r -> Node '[ c] m r
onlyOne = id

-- examples
stdoutLn :: MonadIO m => Consumer String m r
stdoutLn =
  forever $ do
    str <- awaitOn i0
    liftIO $ putStrLn str

stdinLn :: MonadIO m => Producer String m r
stdinLn = forever $ liftIO getLine >>= yieldOn i0
