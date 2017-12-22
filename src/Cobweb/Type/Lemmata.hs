{-|
Module: Cobweb.Type.Lemmata
Description: A collection of lemmata used to simplify constraints.
Copyright: 2017 © Ivan Timokhin
License: BSD3
Maintainer: timokhin.iv@gmail.com
Stability: experimental

A collection of lemmata used to simplify constraints.
-}
{-# OPTIONS_HADDOCK show-extensions #-}
{-# LANGUAGE ConstraintKinds #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE PolyKinds #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeOperators #-}

module Cobweb.Type.Lemmata
  ( removeNonEmpty
  ) where

import Cobweb.Type.Combinators (RemoveW(RemS, RemZ))
import Type.Class.Witness (Wit(Wit), Witness((\\)))
import Type.Family.List (Null)

-- | If it is possible to remove an element from the list, the list
-- cannot be empty.
removeNonEmpty :: forall n as bs. RemoveW n as bs -> Wit (Null as ~ 'False)
{-# NOINLINE[0] removeNonEmpty #-}
removeNonEmpty RemZ = Wit
removeNonEmpty (RemS r) = Wit \\ removeNonEmpty r

{-# RULES
"removeNonEmpty 1" removeNonEmpty = remNE1
 #-}

remNE1 :: RemoveW n (a : as) bs -> Wit (Null (a : as) ~ 'False)
{-# INLINE remNE1 #-}
remNE1 _ = Wit
