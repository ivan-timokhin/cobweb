{-# LANGUAGE ScopedTypeVariables #-}

module Cobweb.Trans where

import Control.Monad.Morph (MFunctor(hoist))
import Control.Monad.Trans (MonadTrans(lift))

import Cobweb.Core (Node, connects, forsAll, run)
import Cobweb.Internal (unsafeHoist)
import Cobweb.Type.Combinators (All)

distribute ::
     forall m t cs r.
     ( Monad m
     , MonadTrans t
     , MFunctor t
     , Monad (t m)
     , Monad (t (Node cs m))
     , All Functor cs
     )
  => Node cs (t m) r
  -> t (Node cs m) r
distribute node
  -- Here's an explanation:
  --
  -- First, we insert a fresh 'Node' layer beneath @t@
  -- (so Node (t m) --> Node (t (Node m))).  This is the hoisting part.
  --
  -- Second, we iterate over old connections via 'forsAll', and move
  -- them all to the new 'Node' layer.  This is the lift.lift part.
  --
  -- Finally, now that the outer layer has no outstanding connections,
  -- we simply run it.
 = run $ forsAll (unsafeHoist (hoist lift) node) (lift . lift . connects)
