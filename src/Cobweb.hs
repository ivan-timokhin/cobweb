{-|
Module: Cobweb
Description: Main entry point to the library.
Copyright: 2017 © Ivan Timokhin
License: BSD3
Maintainer: timokhin.iv@gmail.com
Stability: experimental

This is an umbrella module that re-exports some types and functions
from various @Cobweb.*@ submodules.  Each section begins with a link
to the module of origin for re-exported names in that section.  If a
more tutorial-style introduction is needed, consult "Cobweb.Tutorial".
-}
module Cobweb
  ( -- * Core types and functionality
    -- $core
    -- ** Types
    Node
  , Effect
  , Tube
  , Leaf
  , Awaiting
  , Yielding
    -- ** Functions
    -- *** Running
  , run
    -- *** Initiating connections
  , connectsOn
  , yieldOn
  , eachOn
  , awaitOn
    -- *** Looping
  , forsOn
  , forsOnLeaf
  , forOn
  , forOnLeaf
  , preforOn
  , preforOnLeaf
    -- * Producers
    -- $producers
  , Producer
    -- ** Initiating connections
  , yield
  , each
  , generate
    -- ** Looping
  , for
    -- ** Embedding
  , produceOn
    -- * Consumers
    -- $consumers
  , Consumer
    -- ** Initiating connections
  , await
  , drain
    -- ** Looping
  , prefor
    -- ** Embedding
  , consumeOn
    -- * Pipes
    -- $pipes
  , Pipe
    -- ** Special pipes
  , cat
  , mapping
  , mappingM
  , taking
  , dropping
    -- * Linking
    -- $link
  , Annihilate (annihilate)
  , (>->)
  , (|->)
  , (>-|)
    -- * Folding
    -- $fold
    -- ** Complete folds
  , foldNode
  , foldNode_
  , foldMNode
  , foldMNode_
    -- ** Incomplete folds
  , foldOn
  , foldOn_
  , foldMOn
  , foldMOn_
    -- * Zipping
    -- $zip
  , zipping
  , zipping3
  , zippingWith
  , zippingWith3
    -- * Unzipping
    -- $unzip
  , unzipping
  , unzipping3
  , unzippingWith
  , unzippingWith3
    -- ** Partitioning
  , partitioning
  , partitioningEither
  , partitioningWithEither
    -- * Resource management
    -- $resource
  , runNodeRes
  , region
  , regionC
  , regionE
  , regionCE
    -- * Common channel indices
  , i0
  , i1
  , i2
  , i3
  , i4
  , i5
  , i6
  , i7
  , i8
  , i9
  , i10
  ) where

import Cobweb.Consumer
       (Awaiting, Consumer, await, consumeOn, drain, prefor)
import Cobweb.Core
       (Effect, Leaf, Node, Tube, awaitOn, connectsOn, eachOn, forOn,
        forOnLeaf, forsOn, forsOnLeaf, i0, i1, i10, i2, i3, i4, i5, i6, i7,
        i8, i9, preforOn, preforOnLeaf, run, yieldOn)
import Cobweb.Fold
       (foldMNode, foldMNode_, foldMOn, foldMOn_, foldNode, foldNode_,
        foldOn, foldOn_)
import Cobweb.Link (Annihilate(annihilate), (>->), (>-|), (|->))
import Cobweb.Pipe (Pipe, cat, dropping, mapping, mappingM, taking)
import Cobweb.Producer
       (Producer, Yielding, each, for, generate, produceOn, yield)
import Cobweb.Resource
       (region, regionC, regionCE, regionE, runNodeRes)
import Cobweb.Unzip
       (partitioning, partitioningEither, partitioningWithEither,
        unzipping, unzipping3, unzippingWith, unzippingWith3)
import Cobweb.Zip (zipping, zipping3, zippingWith, zippingWith3)

-- $core
--
-- "Cobweb.Core"

-- $producers
--
-- "Cobweb.Producer"

-- $consumers
--
-- "Cobweb.Consumer"

-- $pipes
--
-- "Cobweb.Pipe"

-- $link
--
-- "Cobweb.Link"

-- $fold
--
-- "Cobweb.Fold"

-- $zip
--
-- "Cobweb.Zip"

-- $unzip
--
-- "Cobweb.Unzip"

-- $resource
--
-- "Cobweb.Resource"
