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
  , appendAll
  , iwithoutRetainsAll
  , ireplacedRetainsAll
  ) where

import Cobweb.Type.Combinators
  ( All
  , Append(appendW)
  , AppendW(AppS, AppZ)
  , IIndex(IIS, IIZ)
  , Remove(removeW)
  , RemoveW(RemS, RemZ)
  , Replace(replaceW)
  , ReplaceW(RepS, RepZ)
  )
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

-- | If all elements of @as@ and all elements of @bs@ satisfy some
-- constraint, then so do all elements in @as 'Type.Family.List.++' bs@.
appendAll ::
     forall p1 p2 p3 f as bs cs. (Append as bs cs, All f as, All f bs)
  => p1 f
  -> p2 as
  -> p3 bs
  -> Wit (All f cs)
{-# NOINLINE[0] appendAll #-}
appendAll _ _ _ = loop (appendW :: AppendW as bs cs)
  where
    loop :: (All f as', All f bs') => AppendW as' bs' cs' -> Wit (All f cs')
    loop AppZ = Wit
    loop (AppS a) = Wit \\ loop a

-- | If all of the elements of the list satisfy some constraint, and
-- one element is removed, remaining elements still satisfy that
-- constraint.
iwithoutRetainsAll ::
     (All f as, Remove n as bs) => p f -> IIndex n as a -> Wit (All f bs)
iwithoutRetainsAll = loop removeW
  where
    loop ::
         All f as => RemoveW n as bs -> p f -> IIndex n as a -> Wit (All f bs)
    loop RemZ _ IIZ = Wit
    loop (RemS r) p (IIS i) = Wit \\ loop r p i

-- | If all of the elements of the list satisfy some constraint, and
-- one of them is replaced by another element that /also/ satisfies
-- that constraint, all elements of the resulting list satisfy that
-- constraint.
ireplacedRetainsAll ::
     forall f as p p' n a b bs. (All f as, f b, Replace n as b bs)
  => p b
  -> p' f
  -> IIndex n as a
  -> Wit (All f bs)
ireplacedRetainsAll _ _ _ = loop (replaceW :: ReplaceW n as b bs)
  where
    loop :: All f as' => ReplaceW n' as' b bs' -> Wit (All f bs')
    loop RepZ = Wit
    loop (RepS r) = Wit \\ loop r
