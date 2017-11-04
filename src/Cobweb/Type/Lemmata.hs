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
  , removeRetainsLength
  , iwithoutRetainsAll
  , ireplacedRetainsAll
  ) where

import Cobweb.Type.Combinators
       (All, Append(appendW), AppendW(AppS, AppZ), IIndex(IIS, IIZ),
        Remove(removeW), RemoveW(RemS, RemZ), Replace(replaceW),
        ReplaceW(RepS, RepZ))
import Data.Type.Length (Length(LS))
import Type.Class.Known (Known(known))
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

{-# RULES
"appendAll 0" appendAll = appendAll0
"appendAll 1" appendAll = appendAll1
"appendAll 2" appendAll = appendAll2
"appendAll 3" appendAll = appendAll3
"appendAll 4" appendAll = appendAll4
"appendAll 5" appendAll = appendAll5
"appendAll 6" appendAll = appendAll6
 #-}

appendAll0 :: All f bs => p1 f -> p2 '[] -> p3 bs -> Wit (All f bs)
{-# INLINE appendAll0 #-}
appendAll0 _ _ _ = Wit

appendAll1 ::
     (f a0, All f bs) => p1 f -> p2 '[ a0] -> p3 bs -> Wit (All f (a0 : bs))
{-# INLINE appendAll1 #-}
appendAll1 _ _ _ = Wit

appendAll2 ::
     (f a0, f a1, All f bs)
  => p1 f
  -> p2 '[ a0, a1]
  -> p3 bs
  -> Wit (All f (a0 : a1 : bs))
{-# INLINE appendAll2 #-}
appendAll2 _ _ _ = Wit

appendAll3 ::
     (f a0, f a1, f a2, All f bs)
  => p1 f
  -> p2 '[ a0, a1, a2]
  -> p3 bs
  -> Wit (All f (a0 : a1 : a2 : bs))
{-# INLINE appendAll3 #-}
appendAll3 _ _ _ = Wit

appendAll4 ::
     (f a0, f a1, f a2, f a3, All f bs)
  => p1 f
  -> p2 '[ a0, a1, a2, a3]
  -> p3 bs
  -> Wit (All f (a0 : a1 : a2 : a3 : bs))
{-# INLINE appendAll4 #-}
appendAll4 _ _ _ = Wit

appendAll5 ::
     (f a0, f a1, f a2, f a3, f a4, All f bs)
  => p1 f
  -> p2 '[ a0, a1, a2, a3, a4]
  -> p3 bs
  -> Wit (All f (a0 : a1 : a2 : a3 : a4 : bs))
{-# INLINE appendAll5 #-}
appendAll5 _ _ _ = Wit

appendAll6 ::
     (f a0, f a1, f a2, f a3, f a4, f a5, All f bs)
  => p1 f
  -> p2 '[ a0, a1, a2, a3, a4, a5]
  -> p3 bs
  -> Wit (All f (a0 : a1 : a2 : a3 : a4 : a5 : bs))
{-# INLINE appendAll6 #-}
appendAll6 _ _ _ = Wit

-- | Removing an element from the list retains the knowledge of list's
-- length.
removeRetainsLength ::
     forall n as bs. (Known Length as)
  => RemoveW n as bs
  -> Wit (Known Length bs)
{-# NOINLINE[0] removeRetainsLength #-}
removeRetainsLength = loop (known :: Length as)
  where
    loop :: Length as' -> RemoveW n' as' bs' -> Wit (Known Length bs')
    loop l RemZ = Wit \\ l
    loop (LS l) (RemS r) = Wit \\ loop l r

{-# RULES
"removeRetainsLength 0" removeRetainsLength = remRetL0
"removeRetainsLength 1" removeRetainsLength = remRetL1
"removeRetainsLength 2" removeRetainsLength = remRetL2
"removeRetainsLength 3" removeRetainsLength = remRetL3
"removeRetainsLength 4" removeRetainsLength = remRetL4
"removeRetainsLength 5" removeRetainsLength = remRetL5
"removeRetainsLength 6" removeRetainsLength = remRetL6
 #-}

remRetL0 :: RemoveW n as '[] -> Wit (Known Length '[])
{-# INLINE remRetL0 #-}
remRetL0 _ = Wit

remRetL1 :: RemoveW n as '[a] -> Wit (Known Length '[a])
{-# INLINE remRetL1 #-}
remRetL1 _ = Wit

remRetL2 :: RemoveW n as '[ a0, a1] -> Wit (Known Length '[ a0, a1])
{-# INLINE remRetL2 #-}
remRetL2 _ = Wit

remRetL3 :: RemoveW n as '[ a0, a1, a2] -> Wit (Known Length '[ a0, a1, a2])
{-# INLINE remRetL3 #-}
remRetL3 _ = Wit

remRetL4 ::
     RemoveW n as '[ a0, a1, a2, a3] -> Wit (Known Length '[ a0, a1, a2, a3])
{-# INLINE remRetL4 #-}
remRetL4 _ = Wit

remRetL5 ::
     RemoveW n as '[ a0, a1, a2, a3, a4]
  -> Wit (Known Length '[ a0, a1, a2, a3, a4])
{-# INLINE remRetL5 #-}
remRetL5 _ = Wit

remRetL6 ::
     RemoveW n as '[ a0, a1, a2, a3, a4, a5]
  -> Wit (Known Length '[ a0, a1, a2, a3, a4, a6])
{-# INLINE remRetL6 #-}
remRetL6 _ = Wit

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
