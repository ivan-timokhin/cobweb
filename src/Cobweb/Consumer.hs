{-# LANGUAGE DataKinds #-}

module Cobweb.Consumer where

import Cobweb.Core (Awaiting)
import Cobweb.Internal (Node)

type Consumer a = Node '[ Awaiting a]
