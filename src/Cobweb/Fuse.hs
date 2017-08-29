{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE DataKinds #-}

module Cobweb.Fuse where

import Type.Family.Nat (NatEq)

import Cobweb.Core (mapsAll)
import Cobweb.Internal (Node)
import Cobweb.Type.Combinators (All, IIndex, IWithout, fuse)

fuseCons ::
     (IWithout n cs cs', NatEq n k ~ 'False, Functor m, All Functor cs)
  => IIndex n cs c
  -> IIndex k cs c
  -> Node cs m r
  -> Node cs' m r
fuseCons n k = mapsAll (fuse n k)
