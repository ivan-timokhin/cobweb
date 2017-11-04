{-|
Module: Cobweb.Type.Combinators
Description: Some utility types for type list manipulations
Copyright: 2017 © Ivan Timokhin
License: BSD3
Maintainer: timokhin.iv@gmail.com
Stability: experimental

This module contains some extensions to the @type-combinators@ package
that are used in implementation and interface of the library.
-}
{-# OPTIONS_HADDOCK show-extensions #-}
{-# LANGUAGE ConstraintKinds #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE EmptyCase #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE FunctionalDependencies #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE PolyKinds #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE UndecidableInstances #-}

module Cobweb.Type.Combinators
  (
    -- * Functor sum
    FSum(FInL, FInR)
  , absurdFSum
    -- * Indices
  , IIndex(IIZ, IIS)
  , forgetIdx
  , lastIndex
    -- ** Small indices
    -- $small
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
    -- * Removing elements
  , Remove(removeW)
  , RemoveW(RemZ, RemS)
    -- * Replacing elements
  , Replace(replaceW)
  , ReplaceW(RepZ, RepS)
  , replaceIdx
  , Append(appendW)
  , AppendW(AppZ, AppS)
    -- * Manipulating 'FSum'
  , fsumOnly
  , fdecompIdx
  , fdecompReplaceIdx
  , freplaceIdx
  , finjectIdx
  , finl
  , finr
  , fuseSum
  , fuseSumWith
  , fuseSumAll
    -- * Type synonyms
  , All
  ) where

import Data.Bifunctor (first)
import Data.Type.Equality ((:~:), type (==))
import Data.Type.Index (Index(IS, IZ))
import Data.Type.Length (Length(LS, LZ))
import Type.Class.Known (Known(known))
import Type.Class.Witness (Witness((\\)))
import Type.Family.List (type (<$>), Last, ListC, Null)
import Type.Family.Nat
       (Len, N(S, Z), N0, N1, N10, N2, N3, N4, N5, N6, N7, N8, N9, Pred)

-- | A sum of a list of functors.
data FSum (fs :: [k -> *]) (a :: k) where
  -- | The sum is represented by the head of the list.
  FInL :: !(f a) -> FSum (f : fs) a
  -- | The sum is represented by the tail of the list.
  FInR :: !(FSum fs a) -> FSum (f : fs) a

-- | A sum of empty list is uninhabited, except for bottom.
absurdFSum :: FSum '[] a -> b
{-# INLINE absurdFSum #-}
absurdFSum x = case x of {}

instance All Functor fs => Functor (FSum fs) where
  fmap = map_

map_ :: All Functor fs => (a -> b) -> FSum fs a -> FSum fs b
{-# INLINE[0] map_ #-}
map_ f (FInL x) = FInL (fmap f x)
map_ f (FInR x) = FInR (map_ f x)

-- Fun facts time!  One specialisation more, and GHC is no longer able
-- to derive @Functor f6@ from @All Functor [..]@
{-# RULES
"fsum/fmap0" map_ = map0_
"fsum/fmap1" map_ = map1_
"fsum/fmap2" map_ = map2_
"fsum/fmap3" map_ = map3_
"fsum/fmap4" map_ = map4_
"fsum/fmap5" map_ = map5_
"fsum/fmap6" map_ = map6_
 #-}

map0_ :: (a -> b) -> FSum '[] a -> FSum '[] b
{-# INLINE map0_ #-}
map0_ _ = absurdFSum

map1_ :: Functor f => (a -> b) -> FSum '[ f] a -> FSum '[ f] b
{-# INLINE map1_ #-}
map1_ f (FInL x) = FInL (fmap f x)
map1_ _ (FInR x) = absurdFSum x

map2_ ::
     (Functor f0, Functor f1)
  => (a -> b)
  -> FSum '[ f0, f1] a
  -> FSum '[ f0, f1] b
{-# INLINE map2_ #-}
map2_ f (FInL x) = FInL (fmap f x)
map2_ f (FInR x) = FInR (map1_ f x)

map3_ ::
     (Functor f0, Functor f1, Functor f2)
  => (a -> b)
  -> FSum '[ f0, f1, f2] a
  -> FSum '[ f0, f1, f2] b
{-# INLINE map3_ #-}
map3_ f (FInL x) = FInL (fmap f x)
map3_ f (FInR x) = FInR (map2_ f x)

map4_ ::
     (Functor f0, Functor f1, Functor f2, Functor f3)
  => (a -> b)
  -> FSum '[ f0, f1, f2, f3] a
  -> FSum '[ f0, f1, f2, f3] b
{-# INLINE map4_ #-}
map4_ f (FInL x) = FInL (fmap f x)
map4_ f (FInR x) = FInR (map3_ f x)

map5_ ::
     (Functor f0, Functor f1, Functor f2, Functor f3, Functor f4)
  => (a -> b)
  -> FSum '[ f0, f1, f2, f3, f4] a
  -> FSum '[ f0, f1, f2, f3, f4] b
{-# INLINE map5_ #-}
map5_ f (FInL x) = FInL (fmap f x)
map5_ f (FInR x) = FInR (map4_ f x)

map6_ ::
     (Functor f0, Functor f1, Functor f2, Functor f3, Functor f4, Functor f5)
  => (a -> b)
  -> FSum '[ f0, f1, f2, f3, f4, f5] a
  -> FSum '[ f0, f1, f2, f3, f4, f5] b
{-# INLINE map6_ #-}
map6_ f (FInL x) = FInL (fmap f x)
map6_ f (FInR x) = FInR (map5_ f x)

-- | A value of type @'IIndex' n as a@ is a witness of a fact that the
-- list @as@ contains element @a@ at position @n@; see 'i0' and others
-- for examples.
--
-- In practice, values of this type are commonly used simply to point
-- out an element in the list, while simultaneously constraining the
-- shape of the list.
data IIndex :: N -> [k] -> k -> * where
  -- | The sought element is the head of the list.
  IIZ :: IIndex 'Z (a : as) a
  -- | The sought element is in the tail of the list.
  IIS :: !(IIndex n as a) -> IIndex ('S n) (b : as) a

absurdIdx :: IIndex n '[] a -> b
{-# INLINE absurdIdx #-}
absurdIdx n = case n of {}

-- | ‘Forget’ the actual index of an element, converting simply to the
-- witness of presence of @a@ /somewhere/ in the list.
--
-- __Note__: the index is, of course, still accessible at the value
-- level; it is merely gone from the types.
forgetIdx :: IIndex n as a -> Index as a
forgetIdx IIZ = IZ
forgetIdx (IIS n) = IS (forgetIdx n)

-- | Indicate last element of a non-empty list with known length.
--
-- The @'Known' 'Length'@ constraint is mostly an implementation
-- detail; any actual type-level list has known length.
lastIndex ::
     forall as. (Known Length as, Null as ~ 'False)
  => IIndex (Pred (Len as)) as (Last as)
{-# NOINLINE[0] lastIndex #-}
lastIndex = loop (known :: Length as)
  where
    loop ::
         (Null as' ~ 'False)
      => Length as'
      -> IIndex (Pred (Len as')) as' (Last as')
    loop (LS LZ) = IIZ
    loop (LS n@(LS _)) = IIS (loop n)

{-# RULES
"fsum/lastIndex/1" lastIndex = lastIndex1
"fsum/lastIndex/2" lastIndex = lastIndex2
"fsum/lastIndex/3" lastIndex = lastIndex3
"fsum/lastIndex/4" lastIndex = lastIndex4
"fsum/lastIndex/5" lastIndex = lastIndex5
"fsum/lastIndex/6" lastIndex = lastIndex6
 #-}

lastIndex1 :: IIndex N0 '[a] a
{-# INLINE lastIndex1 #-}
lastIndex1 = IIZ

lastIndex2 :: IIndex N1 '[a, b] b
{-# INLINE lastIndex2 #-}
lastIndex2 = IIS IIZ

lastIndex3 :: IIndex N2 '[ a0, a1, a2] a2
{-# INLINE lastIndex3 #-}
lastIndex3 = (IIS . IIS) IIZ

lastIndex4 :: IIndex N3 '[ a0, a1, a2, a3] a3
{-# INLINE lastIndex4 #-}
lastIndex4 = (IIS . IIS . IIS) IIZ

lastIndex5 :: IIndex N4 '[ a0, a1, a2, a3, a4] a4
{-# INLINE lastIndex5 #-}
lastIndex5 = (IIS . IIS . IIS . IIS) IIZ

lastIndex6 :: IIndex N5 '[ a0, a1, a2, a3, a4, a5] a5
{-# INLINE lastIndex6 #-}
lastIndex6 = (IIS . IIS . IIS . IIS . IIS) IIZ

-- $small
-- This section contains values of 'IIndex' for small values of @n@.
--
-- Since 'IIndex' has at most one value for each @n@, and the types
-- below are the most generic types of said values, most users should
-- be able to avoid any interaction with constructors of 'IIndex' and
-- just use the values provided here.

i0 :: IIndex N0 (a0 : as) a0
i0 = IIZ

i1 :: IIndex N1 (a0 : a1 : as) a1
i1 = IIS i0

i2 :: IIndex N2 (a0 : a1 : a2 : as) a2
i2 = IIS i1

i3 :: IIndex N3 (a0 : a1 : a2 : a3 : as) a3
i3 = IIS i2

i4 :: IIndex N4 (a0 : a1 : a2 : a3 : a4 : as) a4
i4 = IIS i3

i5 :: IIndex N5 (a0 : a1 : a2 : a3 : a4 : a5 : as) a5
i5 = IIS i4

i6 :: IIndex N6 (a0 : a1 : a2 : a3 : a4 : a5 : a6 : as) a6
i6 = IIS i5

i7 :: IIndex N7 (a0 : a1 : a2 : a3 : a4 : a5 : a6 : a7 : as) a7
i7 = IIS i6

i8 :: IIndex N8 (a0 : a1 : a2 : a3 : a4 : a5 : a6 : a7 : a8 : as) a8
i8 = IIS i7

i9 :: IIndex N9 (a0 : a1 : a2 : a3 : a4 : a5 : a6 : a7 : a8 : a9 : as) a9
i9 = IIS i8

i10 ::
     IIndex N10 (a0 : a1 : a2 : a3 : a4 : a5 : a6 : a7 : a8 : a9 : a10 : as) a10
i10 = IIS i9

-- | Witnesses that @bs@ is @as@ with @n@th element removed.
data RemoveW (n :: N) (as :: [k]) (bs :: [k]) where
  -- | Remove head.
  RemZ :: RemoveW 'Z (a : as) as
  -- | Remove an element in the tail.
  RemS :: !(RemoveW n as bs) -> RemoveW ('S n) (a : as) (a : bs)

absurdRemove :: RemoveW n '[] bs -> a
{-# INLINE absurdRemove #-}
absurdRemove r = case r of {}

-- | A class used to introduce (via functional dependency) @bs@ as
-- @as@ with @n@th element removed.
class Remove n as bs | n as -> bs where
  -- | Witness of the relationship in question.
  removeW :: RemoveW n as bs

instance Remove 'Z (a : as) as where
  removeW = RemZ

instance Remove n as bs => Remove ('S n) (a : as) (a : bs) where
  removeW = RemS removeW

instance Witness () (Remove n as bs) (RemoveW n as bs) where
  x \\ RemZ = x
  x \\ RemS r = x \\ r

-- | Witnesses that @bs@ is @as@ with @n@th element replaced by @b@.
data ReplaceW (n :: N) (as :: [k]) (b :: k) (bs :: [k]) where
  -- | Replace head.
  RepZ :: ReplaceW 'Z (a : as) b (b : as)
  -- | Replace an element in the tail.
  RepS :: !(ReplaceW n as b bs) -> ReplaceW ('S n) (a : as) b (a : bs)

absurdReplace :: ReplaceW n '[] b bs -> a
{-# INLINE absurdReplace #-}
absurdReplace r = case r of {}

-- | A class used to introduce (via functional dependency) @bs@ as
-- @as@ with @n@th element replaced by @b@.
class Replace n as b bs | n as b -> bs where
  -- | Witness of the relationship in question.
  replaceW :: ReplaceW n as b bs

instance Replace 'Z (a : as) b (b : as) where
  replaceW = RepZ

instance Replace n as b bs => Replace ('S n) (a : as) b (a : bs) where
  replaceW = RepS replaceW

instance Witness () (Replace n as b bs) (ReplaceW n as b bs) where
  x \\ RepZ = x
  x \\ RepS r = x \\ r

-- | Witnesses that @cs@ is @as@ and @bs@ concatenated (in value-level
-- lingo, @cs = as ++ bs@).
data AppendW (as :: [k]) (bs :: [k]) (cs :: [k]) where
  -- | Prepend and empty list.
  AppZ :: AppendW '[] as as
  -- | Prepend a non-empty list.
  AppS :: !(AppendW as bs cs) -> AppendW (a : as) bs (a : cs)

-- | A class used to introduce (via functional dependency) @cs@ as
-- @bs@ appended to @as@ (in value-level lingo, @cs = as ++ bs@).
class Append as bs cs | as bs -> cs where
  -- | Witness of the relationship in question.
  appendW :: AppendW as bs cs

instance Append '[] as as where
  appendW = AppZ

instance Append as bs cs => Append (a : as) bs (a : cs) where
  appendW = AppS appendW

instance Witness () (Append as bs cs) (AppendW as bs cs) where
  x \\ AppZ = x
  x \\ AppS a = x \\ a

-- | Produce an index of a replaced element in the new list.
replaceIdx ::
     forall n a as b bs. Replace n as b bs
  => IIndex n as a
  -> IIndex n bs b
{-# INLINE replaceIdx #-}
replaceIdx _ = replaceIdxW (replaceW :: ReplaceW n as b bs)

replaceIdxW :: ReplaceW n as b bs -> IIndex n bs b
{-# NOINLINE[0] replaceIdxW #-}
replaceIdxW RepZ = IIZ
replaceIdxW (RepS r) = IIS (replaceIdxW r)

{-# RULES
"fsum/replaceIdx/1" replaceIdxW = replaceIdxW1
"fsum/replaceIdx/2" replaceIdxW = replaceIdxW2
"fsum/replaceIdx/3" replaceIdxW = replaceIdxW3
"fsum/replaceIdx/4" replaceIdxW = replaceIdxW4
"fsum/replaceIdx/5" replaceIdxW = replaceIdxW5
"fsum/replaceIdx/6" replaceIdxW = replaceIdxW6
 #-}

replaceIdxW1 :: ReplaceW n '[a] b bs -> IIndex n bs b
{-# INLINE replaceIdxW1 #-}
replaceIdxW1 RepZ = IIZ
replaceIdxW1 (RepS r) = absurdReplace r

replaceIdxW2 :: ReplaceW n '[ a0, a1] b bs -> IIndex n bs b
{-# INLINE replaceIdxW2 #-}
replaceIdxW2 RepZ = IIZ
replaceIdxW2 (RepS r) = IIS (replaceIdxW1 r)

replaceIdxW3 :: ReplaceW n '[ a0, a1, a2] b bs -> IIndex n bs b
{-# INLINE replaceIdxW3 #-}
replaceIdxW3 RepZ = IIZ
replaceIdxW3 (RepS r) = IIS (replaceIdxW2 r)

replaceIdxW4 :: ReplaceW n '[ a0, a1, a2, a3] b bs -> IIndex n bs b
{-# INLINE replaceIdxW4 #-}
replaceIdxW4 RepZ = IIZ
replaceIdxW4 (RepS r) = IIS (replaceIdxW3 r)

replaceIdxW5 :: ReplaceW n '[ a0, a1, a2, a3, a4] b bs -> IIndex n bs b
{-# INLINE replaceIdxW5 #-}
replaceIdxW5 RepZ = IIZ
replaceIdxW5 (RepS r) = IIS (replaceIdxW4 r)

replaceIdxW6 :: ReplaceW n '[ a0, a1, a2, a3, a4, a5] b bs -> IIndex n bs b
{-# INLINE replaceIdxW6 #-}
replaceIdxW6 RepZ = IIZ
replaceIdxW6 (RepS r) = IIS (replaceIdxW5 r)

-- | Extract the only term of a single-term sum.
fsumOnly :: FSum '[f] a -> f a
{-# INLINE fsumOnly #-}
fsumOnly (FInL f) = f
fsumOnly (FInR f) = absurdFSum f

-- | Decompose the sum into either an element at the specific index,
-- or some element from the rest of the sum.
--
-- This function is perhaps easier to understand by looking at the
-- types inferred for various values of the first parameter (which
-- also serves as a demonstration of how values of 'IIndex' can be
-- used do discharge other types of constraints from this module):
--
-- @
-- 'fdecompIdx' 'i0' :: 'FSum' (f : fs) -> 'Either' ('FSum' fs a) (f a)
-- 'fdecompIdx' 'i1' :: 'FSum' (f0 : f1 : fs) -> 'Either' ('FSum' (f0 : fs) a) (f1 a)
-- 'fdecompIdx' 'i2' :: 'FSum' (f0 : f1 : f2 : fs) -> 'Either' ('FSum' (f0 : f1 : fs) a) (f2 a)
-- @
--
-- And so on.  In all cases, 'Left' means that the sum is not
-- represented by the element requested, and 'Right' that it is.
fdecompIdx ::
     Remove n fs gs
  => IIndex n fs f -- ^ An index of an element to be extracted
  -> FSum fs a
  -> Either (FSum gs a) (f a)
{-# INLINE fdecompIdx #-}
fdecompIdx = fdecompIdx_W removeW

fdecompIdx_W ::
     RemoveW n fs gs
  -> IIndex n fs f
  -> FSum fs a
  -> Either (FSum gs a) (f a)
{-# NOINLINE[0] fdecompIdx_W #-}
fdecompIdx_W RemZ IIZ (FInL x) = Right x
fdecompIdx_W RemZ IIZ (FInR x) = Left x
fdecompIdx_W (RemS _) (IIS _) (FInL x) = Left (FInL x)
fdecompIdx_W (RemS r) (IIS n) (FInR x) = first FInR (fdecompIdx_W r n x)

{-# RULES
"fdecompIdx_W/0" fdecompIdx_W = decompIdx_0
"fdecompIdx_W/1" fdecompIdx_W = decompIdx_1
"fdecompIdx_W/2" fdecompIdx_W = decompIdx_2
"fdecompIdx_W/3" fdecompIdx_W = decompIdx_3
"fdecompIdx_W/4" fdecompIdx_W = decompIdx_4
"fdecompIdx_W/5" fdecompIdx_W = decompIdx_5
"fdecompIdx_W/6" fdecompIdx_W = decompIdx_6
 #-}

decompIdx_0 ::
     RemoveW n '[] gs
  -> IIndex n '[] f
  -> FSum '[] a
  -> Either (FSum gs a) (f a)
{-# INLINE decompIdx_0 #-}
decompIdx_0 _ _ = absurdFSum

decompIdx_1 ::
     RemoveW n '[ f0] gs
  -> IIndex n '[ f0] f
  -> FSum '[ f0] a
  -> Either (FSum gs a) (f a)
{-# INLINE decompIdx_1 #-}
decompIdx_1 RemZ IIZ (FInL x) = Right x
decompIdx_1 RemZ IIZ (FInR x) = absurdFSum x
decompIdx_1 (RemS r) (IIS _) _ = absurdRemove r

decompIdx_2 ::
     RemoveW n '[ f0, f1] gs
  -> IIndex n '[ f0, f1] f
  -> FSum '[ f0, f1] a
  -> Either (FSum gs a) (f a)
{-# INLINE decompIdx_2 #-}
decompIdx_2 RemZ IIZ (FInL x) = Right x
decompIdx_2 RemZ IIZ (FInR x) = Left x
decompIdx_2 (RemS _) (IIS _) (FInL x) = Left (FInL x)
decompIdx_2 (RemS r) (IIS n) (FInR x) = first FInR (decompIdx_1 r n x)

decompIdx_3 ::
     RemoveW n '[ f0, f1, f2] gs
  -> IIndex n '[ f0, f1, f2] f
  -> FSum '[ f0, f1, f2] a
  -> Either (FSum gs a) (f a)
{-# INLINE decompIdx_3 #-}
decompIdx_3 RemZ IIZ (FInL x) = Right x
decompIdx_3 RemZ IIZ (FInR x) = Left x
decompIdx_3 (RemS _) (IIS _) (FInL x) = Left (FInL x)
decompIdx_3 (RemS r) (IIS n) (FInR x) = first FInR (decompIdx_2 r n x)

decompIdx_4 ::
     RemoveW n '[ f0, f1, f2, f3] gs
  -> IIndex n '[ f0, f1, f2, f3] f
  -> FSum '[ f0, f1, f2, f3] a
  -> Either (FSum gs a) (f a)
{-# INLINE decompIdx_4 #-}
decompIdx_4 RemZ IIZ (FInL x) = Right x
decompIdx_4 RemZ IIZ (FInR x) = Left x
decompIdx_4 (RemS _) (IIS _) (FInL x) = Left (FInL x)
decompIdx_4 (RemS r) (IIS n) (FInR x) = first FInR (decompIdx_3 r n x)

decompIdx_5 ::
     RemoveW n '[ f0, f1, f2, f3, f4] gs
  -> IIndex n '[ f0, f1, f2, f3, f4] f
  -> FSum '[ f0, f1, f2, f3, f4] a
  -> Either (FSum gs a) (f a)
{-# INLINE decompIdx_5 #-}
decompIdx_5 RemZ IIZ (FInL x) = Right x
decompIdx_5 RemZ IIZ (FInR x) = Left x
decompIdx_5 (RemS _) (IIS _) (FInL x) = Left (FInL x)
decompIdx_5 (RemS r) (IIS n) (FInR x) = first FInR (decompIdx_4 r n x)

decompIdx_6 ::
     RemoveW n '[ f0, f1, f2, f3, f4, f5] gs
  -> IIndex n '[ f0, f1, f2, f3, f4, f5] f
  -> FSum '[ f0, f1, f2, f3, f4, f5] a
  -> Either (FSum gs a) (f a)
{-# INLINE decompIdx_6 #-}
decompIdx_6 RemZ IIZ (FInL x) = Right x
decompIdx_6 RemZ IIZ (FInR x) = Left x
decompIdx_6 (RemS _) (IIS _) (FInL x) = Left (FInL x)
decompIdx_6 (RemS r) (IIS n) (FInR x) = first FInR (decompIdx_5 r n x)

-- | Decompose the sum like 'fdecompIdx', but instead of the sum
-- /without/ the requested element, return the sum with the requested
-- element /replaced/ by an arbitrary other in the even of mismatch.
--
-- Specialised for different index values, the type would look like
-- this:
--
-- @
-- 'fdecompReplaceIdx' 'i0' ::
--    p g -> 'FSum' (f : fs) a -> 'Either' ('FSum' (g : fs) a) (f a)
--
-- 'fdecompReplaceIdx' 'i1' ::
--    p g -> 'FSum' (f0 : f : fs) a -> 'Either' ('FSum' (f0 : g : fs) a) (f a)
--
-- 'fdecompReplaceIdx' 'i2' ::
--    p g -> 'FSum' (f0 : f1 : f : fs) a -> 'Either' ('FSum' (f0 : f1 : g : fs) a) (f a)
-- @
--
-- And so on.
fdecompReplaceIdx ::
     forall n fs f p g gs a. Replace n fs g gs
  => IIndex n fs f
  -> p g
  -> FSum fs a
  -> Either (FSum gs a) (f a)
{-# INLINE fdecompReplaceIdx #-}
fdecompReplaceIdx n _ = fdecompReplaceIdxW (replaceW :: ReplaceW n fs g gs) n

fdecompReplaceIdxW ::
     ReplaceW n fs g gs
  -> IIndex n fs f
  -> FSum fs a
  -> Either (FSum gs a) (f a)
{-# NOINLINE[0] fdecompReplaceIdxW #-}
fdecompReplaceIdxW RepZ IIZ (FInL x) = Right x
fdecompReplaceIdxW RepZ IIZ (FInR x) = Left (FInR x)
fdecompReplaceIdxW (RepS _) (IIS _) (FInL x) = Left (FInL x)
fdecompReplaceIdxW (RepS r) (IIS n) (FInR x) =
  first FInR (fdecompReplaceIdxW r n x)

{-# RULES
"fsum/fdecompReplaceIdxW/0" fdecompReplaceIdxW = fdecompReplaceIdxW0
"fsum/fdecompReplaceIdxW/1" fdecompReplaceIdxW = fdecompReplaceIdxW1
"fsum/fdecompReplaceIdxW/2" fdecompReplaceIdxW = fdecompReplaceIdxW2
"fsum/fdecompReplaceIdxW/3" fdecompReplaceIdxW = fdecompReplaceIdxW3
"fsum/fdecompReplaceIdxW/4" fdecompReplaceIdxW = fdecompReplaceIdxW4
"fsum/fdecompReplaceIdxW/5" fdecompReplaceIdxW = fdecompReplaceIdxW5
"fsum/fdecompReplaceIdxW/6" fdecompReplaceIdxW = fdecompReplaceIdxW6
 #-}

fdecompReplaceIdxW0 ::
     ReplaceW n '[] g gs
  -> IIndex n '[] f
  -> FSum '[] a
  -> Either (FSum gs a) (f a)
{-# INLINE fdecompReplaceIdxW0 #-}
fdecompReplaceIdxW0 _ _ = absurdFSum

fdecompReplaceIdxW1 ::
     ReplaceW n '[ f0] g gs
  -> IIndex n '[ f0] f
  -> FSum '[ f0] a
  -> Either (FSum gs a) (f a)
{-# INLINE fdecompReplaceIdxW1 #-}
fdecompReplaceIdxW1 RepZ IIZ (FInL x) = Right x
fdecompReplaceIdxW1 RepZ IIZ (FInR x) = absurdFSum x
fdecompReplaceIdxW1 (RepS r) _ _ = absurdReplace r

fdecompReplaceIdxW2 ::
     ReplaceW n '[ f0, f1] g gs
  -> IIndex n '[ f0, f1] f
  -> FSum '[ f0, f1] a
  -> Either (FSum gs a) (f a)
{-# INLINE fdecompReplaceIdxW2 #-}
fdecompReplaceIdxW2 RepZ IIZ (FInL x) = Right x
fdecompReplaceIdxW2 RepZ IIZ (FInR x) = Left (FInR x)
fdecompReplaceIdxW2 (RepS _) (IIS _) (FInL x) = Left (FInL x)
fdecompReplaceIdxW2 (RepS r) (IIS n) (FInR x) =
  first FInR (fdecompReplaceIdxW1 r n x)

fdecompReplaceIdxW3 ::
     ReplaceW n '[ f0, f1, f2] g gs
  -> IIndex n '[ f0, f1, f2] f
  -> FSum '[ f0, f1, f2] a
  -> Either (FSum gs a) (f a)
{-# INLINE fdecompReplaceIdxW3 #-}
fdecompReplaceIdxW3 RepZ IIZ (FInL x) = Right x
fdecompReplaceIdxW3 RepZ IIZ (FInR x) = Left (FInR x)
fdecompReplaceIdxW3 (RepS _) (IIS _) (FInL x) = Left (FInL x)
fdecompReplaceIdxW3 (RepS r) (IIS n) (FInR x) =
  first FInR (fdecompReplaceIdxW2 r n x)

fdecompReplaceIdxW4 ::
     ReplaceW n '[ f0, f1, f2, f3] g gs
  -> IIndex n '[ f0, f1, f2, f3] f
  -> FSum '[ f0, f1, f2, f3] a
  -> Either (FSum gs a) (f a)
{-# INLINE fdecompReplaceIdxW4 #-}
fdecompReplaceIdxW4 RepZ IIZ (FInL x) = Right x
fdecompReplaceIdxW4 RepZ IIZ (FInR x) = Left (FInR x)
fdecompReplaceIdxW4 (RepS _) (IIS _) (FInL x) = Left (FInL x)
fdecompReplaceIdxW4 (RepS r) (IIS n) (FInR x) =
  first FInR (fdecompReplaceIdxW3 r n x)

fdecompReplaceIdxW5 ::
     ReplaceW n '[ f0, f1, f2, f3, f4] g gs
  -> IIndex n '[ f0, f1, f2, f3, f4] f
  -> FSum '[ f0, f1, f2, f3, f4] a
  -> Either (FSum gs a) (f a)
{-# INLINE fdecompReplaceIdxW5 #-}
fdecompReplaceIdxW5 RepZ IIZ (FInL x) = Right x
fdecompReplaceIdxW5 RepZ IIZ (FInR x) = Left (FInR x)
fdecompReplaceIdxW5 (RepS _) (IIS _) (FInL x) = Left (FInL x)
fdecompReplaceIdxW5 (RepS r) (IIS n) (FInR x) =
  first FInR (fdecompReplaceIdxW4 r n x)

fdecompReplaceIdxW6 ::
     ReplaceW n '[ f0, f1, f2, f3, f4, f5] g gs
  -> IIndex n '[ f0, f1, f2, f3, f4, f5] f
  -> FSum '[ f0, f1, f2, f3, f4, f5] a
  -> Either (FSum gs a) (f a)
{-# INLINE fdecompReplaceIdxW6 #-}
fdecompReplaceIdxW6 RepZ IIZ (FInL x) = Right x
fdecompReplaceIdxW6 RepZ IIZ (FInR x) = Left (FInR x)
fdecompReplaceIdxW6 (RepS _) (IIS _) (FInL x) = Left (FInL x)
fdecompReplaceIdxW6 (RepS r) (IIS n) (FInR x) =
  first FInR (fdecompReplaceIdxW5 r n x)

-- | Replace one functor in the 'FSum' by another by transforming the
-- old one into a new one.
--
-- Specialised for different values of the first parameter, the type
-- of the function looks like this:
--
-- @
-- 'freplaceIdx' 'i0' :: (f0 a -> g a) -> 'FSum' (f0 : fs) a -> 'FSum' (g : fs) a
-- 'freplaceIdx' 'i1' :: (f1 a -> g a) -> 'FSum' (f0 : f1 : fs) a -> 'FSum' (f0 : g : fs)
-- @
--
-- And so on.
--
-- Note that the transformation function cannot change the type of the
-- contained value, as, if the supplied sum is not represented by the
-- functor at requested index, the old value will be used (and the
-- supplied function won't be called).
freplaceIdx ::
     forall n fs f g gs a. Replace n fs g gs
  => IIndex n fs f -- ^ An index of a functor to be replaced.
  -> (f a -> g a) -- ^ A function used to transform old functor into a
     -- new one.
  -> FSum fs a -- ^ An old sum, which may or may not be represented by
     -- the functor in question.
  -> FSum gs a
{-# NOINLINE freplaceIdx #-}
freplaceIdx = freplaceIdxW replaceW

{-# RULES "fsum/freplaceIdx" freplaceIdx = freplaceIdxW replaceW #-}

freplaceIdxW ::
     forall n fs f g gs a.
     ReplaceW n fs g gs
  -> IIndex n fs f
  -> (f a -> g a)
  -> FSum fs a
  -> FSum gs a
{-# NOINLINE[0] freplaceIdxW #-}
freplaceIdxW n r f = loop n r
  where
    loop :: ReplaceW n' fs' g gs' -> IIndex n' fs' f -> FSum fs' a -> FSum gs' a
    loop RepZ IIZ (FInL x) = FInL (f x)
    loop RepZ IIZ (FInR x) = FInR x
    loop (RepS _) (IIS _) (FInL x) = FInL x
    loop (RepS r') (IIS n') (FInR x) = FInR (loop r' n' x)

{-# RULES
"fsum/freplaceIdx/0" freplaceIdxW = freplaceIdxW0
"fsum/freplaceIdx/1" freplaceIdxW = freplaceIdxW1
"fsum/freplaceIdx/2" freplaceIdxW = freplaceIdxW2
"fsum/freplaceIdx/3" freplaceIdxW = freplaceIdxW3
"fsum/freplaceIdx/4" freplaceIdxW = freplaceIdxW4
"fsum/freplaceIdx/5" freplaceIdxW = freplaceIdxW5
"fsum/freplaceIdx/6" freplaceIdxW = freplaceIdxW6
 #-}

freplaceIdxW0 ::
     ReplaceW n '[] g gs
  -> IIndex n '[] f
  -> (f a -> g a)
  -> FSum '[] a
  -> FSum gs a
{-# INLINE freplaceIdxW0 #-}
freplaceIdxW0 _ _ _ = absurdFSum

freplaceIdxW1 ::
     ReplaceW n '[ f0] g gs
  -> IIndex n '[ f0] f
  -> (f a -> g a)
  -> FSum '[ f0] a
  -> FSum gs a
{-# INLINE freplaceIdxW1 #-}
freplaceIdxW1 RepZ IIZ f (FInL x) = FInL (f x)
freplaceIdxW1 RepZ IIZ _ (FInR x) = absurdFSum x
freplaceIdxW1 (RepS r) _ _ _ = absurdReplace r

freplaceIdxW2 ::
     ReplaceW n '[ f0, f1] g gs
  -> IIndex n '[ f0, f1] f
  -> (f a -> g a)
  -> FSum '[ f0, f1] a
  -> FSum gs a
{-# INLINE freplaceIdxW2 #-}
freplaceIdxW2 RepZ IIZ f (FInL x) = FInL (f x)
freplaceIdxW2 RepZ IIZ _ (FInR x) = FInR x
freplaceIdxW2 (RepS _) (IIS _) _ (FInL x) = FInL x
freplaceIdxW2 (RepS r) (IIS n) f (FInR x) = FInR (freplaceIdxW1 r n f x)

freplaceIdxW3 ::
     ReplaceW n '[ f0, f1, f2] g gs
  -> IIndex n '[ f0, f1, f2] f
  -> (f a -> g a)
  -> FSum '[ f0, f1, f2] a
  -> FSum gs a
{-# INLINE freplaceIdxW3 #-}
freplaceIdxW3 RepZ IIZ f (FInL x) = FInL (f x)
freplaceIdxW3 RepZ IIZ _ (FInR x) = FInR x
freplaceIdxW3 (RepS _) (IIS _) _ (FInL x) = FInL x
freplaceIdxW3 (RepS r) (IIS n) f (FInR x) = FInR (freplaceIdxW2 r n f x)

freplaceIdxW4 ::
     ReplaceW n '[ f0, f1, f2, f3] g gs
  -> IIndex n '[ f0, f1, f2, f3] f
  -> (f a -> g a)
  -> FSum '[ f0, f1, f2, f3] a
  -> FSum gs a
{-# INLINE freplaceIdxW4 #-}
freplaceIdxW4 RepZ IIZ f (FInL x) = FInL (f x)
freplaceIdxW4 RepZ IIZ _ (FInR x) = FInR x
freplaceIdxW4 (RepS _) (IIS _) _ (FInL x) = FInL x
freplaceIdxW4 (RepS r) (IIS n) f (FInR x) = FInR (freplaceIdxW3 r n f x)

freplaceIdxW5 ::
     ReplaceW n '[ f0, f1, f2, f3, f4] g gs
  -> IIndex n '[ f0, f1, f2, f3, f4] f
  -> (f a -> g a)
  -> FSum '[ f0, f1, f2, f3, f4] a
  -> FSum gs a
{-# INLINE freplaceIdxW5 #-}
freplaceIdxW5 RepZ IIZ f (FInL x) = FInL (f x)
freplaceIdxW5 RepZ IIZ _ (FInR x) = FInR x
freplaceIdxW5 (RepS _) (IIS _) _ (FInL x) = FInL x
freplaceIdxW5 (RepS r) (IIS n) f (FInR x) = FInR (freplaceIdxW4 r n f x)

freplaceIdxW6 ::
     ReplaceW n '[ f0, f1, f2, f3, f4, f5] g gs
  -> IIndex n '[ f0, f1, f2, f3, f4, f5] f
  -> (f a -> g a)
  -> FSum '[ f0, f1, f2, f3, f4, f5] a
  -> FSum gs a
{-# INLINE freplaceIdxW6 #-}
freplaceIdxW6 RepZ IIZ f (FInL x) = FInL (f x)
freplaceIdxW6 RepZ IIZ _ (FInR x) = FInR x
freplaceIdxW6 (RepS _) (IIS _) _ (FInL x) = FInL x
freplaceIdxW6 (RepS r) (IIS n) f (FInR x) = FInR (freplaceIdxW5 r n f x)

-- | Inject an element in the sum at the specified position.
--
-- Specialised for different values of first argument, the type looks
-- like this:
--
-- @
-- 'finjectIdx' 'i0' :: f0 a -> 'FSum' (f0 : fs) a
-- 'finjectIdx' 'i1' :: f1 a -> 'FSum' (f0 : f1 : fs) a
-- 'finjectIdx' 'i2' :: f2 a -> 'FSum' (f0 : f1 : f2 : fs) a
-- @
--
-- And so on.
finjectIdx ::
  forall n fs f a.
     IIndex n fs f -- ^ An index at which to inject the functor.
  -> f a -- ^ The value to be injected.
  -> FSum fs a -- ^ A sum represented by the provided value at the
     -- provided index.
{-# NOINLINE[0] finjectIdx #-}
finjectIdx n f = loop n
  where
    loop :: IIndex n' fs' f -> FSum fs' a
    loop IIZ = FInL f
    loop (IIS n') = FInR (loop n')

{-# RULES
"finjectIdx/1" finjectIdx = inject1
"finjectIdx/2" finjectIdx = inject2
"finjectIdx/3" finjectIdx = inject3
"finjectIdx/4" finjectIdx = inject4
"finjectIdx/5" finjectIdx = inject5
"finjectIdx/6" finjectIdx = inject6
 #-}

inject1 :: IIndex n '[ f0] f -> f a -> FSum '[ f0] a
{-# INLINE inject1 #-}
inject1 IIZ = FInL
inject1 (IIS n) = absurdIdx n

inject2 :: IIndex n '[ f0, f1] f -> f a -> FSum '[ f0, f1] a
{-# INLINE inject2 #-}
inject2 IIZ = FInL
inject2 (IIS n) = FInR . inject1 n

inject3 :: IIndex n '[ f0, f1, f2] f -> f a -> FSum '[ f0, f1, f2] a
{-# INLINE inject3 #-}
inject3 IIZ = FInL
inject3 (IIS n) = FInR . inject2 n

inject4 :: IIndex n '[ f0, f1, f2, f3] f -> f a -> FSum '[ f0, f1, f2, f3] a
{-# INLINE inject4 #-}
inject4 IIZ = FInL
inject4 (IIS n) = FInR . inject3 n

inject5 ::
     IIndex n '[ f0, f1, f2, f3, f4] f -> f a -> FSum '[ f0, f1, f2, f3, f4] a
{-# INLINE inject5 #-}
inject5 IIZ = FInL
inject5 (IIS n) = FInR . inject4 n

inject6 ::
     IIndex n '[ f0, f1, f2, f3, f4, f5] f
  -> f a
  -> FSum '[ f0, f1, f2, f3, f4, f5] a
{-# INLINE inject6 #-}
inject6 IIZ = FInL
inject6 (IIS n) = FInR . inject5 n

-- | Embed a sum into a sum of a larger list, obtained by adding
-- elements on the right.
--
-- This function does not, in a sense, change the /value/ stored, only
-- its /type/.
--
-- Since the 'Type.Family.List.++' type family is not injective, a
-- proxy argument is used to guide type inference.
finl :: Append fs gs hs => proxy gs -> FSum fs a -> FSum hs a
{-# NOINLINE finl #-}
finl = loop appendW
  where
    loop :: AppendW fs gs hs -> p gs -> FSum fs a -> FSum hs a
    loop (AppS _) _ (FInL x) = FInL x
    loop (AppS a) p (FInR x) = FInR (loop a p x)
    loop AppZ _ fsum = absurdFSum fsum

{-# RULES
"finl/0" finl = finl0
"finl/1" finl = finl1
"finl/2" finl = finl2
"finl/3" finl = finl3
"finl/4" finl = finl4
"finl/5" finl = finl5
"finl/6" finl = finl6
 #-}

finl0 :: proxy gs -> FSum '[] a -> FSum gs a
{-# INLINE finl0 #-}
finl0 _ = absurdFSum

finl1 :: proxy gs -> FSum '[ f0] a -> FSum (f0 : gs) a
{-# INLINE finl1 #-}
finl1 _ (FInL x) = FInL x
finl1 p (FInR x) = FInR (finl0 p x)

finl2 :: proxy gs -> FSum '[ f0, f1] a -> FSum (f0 : f1 : gs) a
{-# INLINE finl2 #-}
finl2 _ (FInL x) = FInL x
finl2 p (FInR x) = FInR (finl1 p x)

finl3 :: proxy gs -> FSum '[ f0, f1, f2] a -> FSum (f0 : f1 : f2 : gs) a
{-# INLINE finl3 #-}
finl3 _ (FInL x) = FInL x
finl3 p (FInR x) = FInR (finl2 p x)

finl4 ::
     proxy gs -> FSum '[ f0, f1, f2, f3] a -> FSum (f0 : f1 : f2 : f3 : gs) a
{-# INLINE finl4 #-}
finl4 _ (FInL x) = FInL x
finl4 p (FInR x) = FInR (finl3 p x)

finl5 ::
     proxy gs
  -> FSum '[ f0, f1, f2, f3, f4] a
  -> FSum (f0 : f1 : f2 : f3 : f4 : gs) a
{-# INLINE finl5 #-}
finl5 _ (FInL x) = FInL x
finl5 p (FInR x) = FInR (finl4 p x)

finl6 ::
     proxy gs
  -> FSum '[ f0, f1, f2, f3, f4, f5] a
  -> FSum (f0 : f1 : f2 : f3 : f4 : f5 : gs) a
{-# INLINE finl6 #-}
finl6 _ (FInL x) = FInL x
finl6 p (FInR x) = FInR (finl5 p x)

-- | Embed a sum into a sum of a larger list, obtained by adding
-- elements of the left.
--
-- This function is similar to 'finl', but, due to right-recursive
-- nature of the 'FSum' definition, requires a @'Known' 'Length'@
-- constraint on the left list.
finr ::
     forall proxy fs gs hs a. Append fs gs hs
  => proxy fs
  -> FSum gs a
  -> FSum hs a
{-# NOINLINE finr #-}
finr _ = loop (appendW :: AppendW fs gs hs)
  where
    loop :: AppendW fs' gs hs' -> FSum gs a -> FSum hs' a
    loop AppZ = id
    loop (AppS app) = FInR . loop app

{-# RULES
"finr/0" finr = finr0
"finr/1" finr = finr1
"finr/2" finr = finr2
"finr/3" finr = finr3
"finr/4" finr = finr4
"finr/5" finr = finr5
"finr/6" finr = finr6
 #-}

finr0 :: proxy '[] -> FSum fs a -> FSum fs a
{-# INLINE finr0 #-}
finr0 _ = id

finr1 :: proxy '[ f0] -> FSum fs a -> FSum (f0 : fs) a
{-# INLINE finr1 #-}
finr1 _ = FInR

finr2 :: proxy '[ f0, f1] -> FSum fs a -> FSum (f0 : f1 : fs) a
{-# INLINE finr2 #-}
finr2 _ = FInR . FInR

finr3 :: proxy '[ f0, f1, f2] -> FSum fs a -> FSum (f0 : f1 : f2 : fs) a
{-# INLINE finr3 #-}
finr3 _ = FInR . FInR . FInR

finr4 ::
     proxy '[ f0, f1, f2, f3] -> FSum fs a -> FSum (f0 : f1 : f2 : f3 : fs) a
{-# INLINE finr4 #-}
finr4 _ = FInR . FInR . FInR . FInR

finr5 ::
     proxy '[ f0, f1, f2, f3, f4]
  -> FSum fs a
  -> FSum (f0 : f1 : f2 : f3 : f4 : fs) a
{-# INLINE finr5 #-}
finr5 _ = FInR . FInR . FInR . FInR . FInR

finr6 ::
     proxy '[ f0, f1, f2, f3, f4, f5]
  -> FSum fs a
  -> FSum (f0 : f1 : f2 : f3 : f4 : f5 : fs) a
{-# INLINE finr6 #-}
finr6 _ = FInR . FInR . FInR . FInR . FInR . FInR

-- | Unify two identical terms in the sum, discarding the first one.
--
-- Note that the terms must be identical as types, they must be
-- distinct /terms of the sum/; i.e. provided indices must be distinct
-- (hence @(n 'Data.Type.Equality.==' m) ~ ''False'@ constraint).
--
-- Specialised to different values of the indices, the type looks like
-- this:
--
-- @
-- 'fuseSum' 'i0' 'i1' :: 'FSum' (f : f : fs) a -> 'FSum' (f : fs) a
-- 'fuseSum' 'i0' 'i2' :: 'FSum' (f : f1 : f : fs) a -> 'FSum' (f1 : f : fs)
-- 'fuseSum' 'i2' 'i0' :: 'FSum' (f : f1 : f : fs) a -> 'FSum' (f : f1 : fs)
-- @
--
-- Trying to call @'fuseSum' 'i0' 'i0'@ and such results in a type
-- error.  Unfortunately, it does not mention indices at all, instead
-- complaining that
--
-- >    • Couldn't match type ‘'True’ with ‘'False’
-- >        arising from a use of ‘fuseSum’
--
-- so if such errors arise, a likely cause is trying to 'fuseSum' a term
-- with itself.
fuseSum ::
     ((n == m) ~ 'False, Remove n fs fs')
  => IIndex n fs f -- ^ The index of the term to be moved.
  -> IIndex m fs f -- ^ The index of the term to be kept.
  -> FSum fs a
  -> FSum fs' a
{-# INLINE fuseSum #-}
fuseSum = fuseSumW removeW

fuseSumW ::
     (n == m) ~ 'False
  => RemoveW n fs fs'
  -> IIndex n fs f
  -> IIndex m fs f
  -> FSum fs a
  -> FSum fs' a
{-# NOINLINE[0] fuseSumW #-}
fuseSumW RemZ IIZ (IIS m) (FInL x) = finjectIdx m x
fuseSumW RemZ IIZ (IIS _) (FInR y) = y
fuseSumW r@(RemS _) n@(IIS _) IIZ fsum =
  case fdecompIdx n fsum \\ r of
    Right x -> FInL x
    Left y -> y
fuseSumW (RemS _) (IIS _) (IIS _) (FInL x) = FInL x
fuseSumW (RemS r) (IIS n) (IIS m) (FInR y) = FInR (fuseSumW r n m y)

{-# RULES
"fsum/fuseSum/2" fuseSumW = fuseSumW2
"fsum/fuseSum/3" fuseSumW = fuseSumW3
"fsum/fuseSum/4" fuseSumW = fuseSumW4
"fsum/fuseSum/5" fuseSumW = fuseSumW5
"fsum/fuseSum/6" fuseSumW = fuseSumW6
 #-}

fuseSumW2 ::
     (n == m) ~ 'False
  => RemoveW n '[ f0, f1] fs
  -> IIndex n '[ f0, f1] f
  -> IIndex m '[ f0, f1] f
  -> FSum '[ f0, f1] a
  -> FSum fs a
{-# INLINE fuseSumW2 #-}
fuseSumW2 RemZ IIZ (IIS IIZ) (FInL x) = FInL x
fuseSumW2 RemZ IIZ (IIS _) (FInR x) = x
fuseSumW2 (RemS RemZ) (IIS IIZ) IIZ (FInL x) = FInL x
fuseSumW2 (RemS RemZ) (IIS IIZ) IIZ (FInR x) = x
fuseSumW2 (RemS (RemS r)) _ _ _ = absurdRemove r
fuseSumW2 _ _ (IIS (IIS m)) _ = absurdIdx m

fuseSumW3 ::
     (n == m) ~ 'False
  => RemoveW n '[ f0, f1, f2] fs
  -> IIndex n '[ f0, f1, f2] f
  -> IIndex m '[ f0, f1, f2] f
  -> FSum '[ f0, f1, f2] a
  -> FSum fs a
{-# INLINE fuseSumW3 #-}
fuseSumW3 RemZ IIZ (IIS m) (FInL x) = inject2 m x
fuseSumW3 RemZ IIZ (IIS _) (FInR x) = x
fuseSumW3 r@(RemS _) n@(IIS _) IIZ fsum =
  case decompIdx_3 r n fsum of
    Right x -> FInL x
    Left x -> x
fuseSumW3 (RemS _) (IIS _) (IIS _) (FInL x) = FInL x
fuseSumW3 (RemS r) (IIS n) (IIS m) (FInR x) = FInR (fuseSumW2 r n m x)

fuseSumW4 ::
     (n == m) ~ 'False
  => RemoveW n '[ f0, f1, f2, f3] fs
  -> IIndex n '[ f0, f1, f2, f3] f
  -> IIndex m '[ f0, f1, f2, f3] f
  -> FSum '[ f0, f1, f2, f3] a
  -> FSum fs a
{-# INLINE fuseSumW4 #-}
fuseSumW4 RemZ IIZ (IIS m) (FInL x) = inject3 m x
fuseSumW4 RemZ IIZ (IIS _) (FInR x) = x
fuseSumW4 r@(RemS _) n@(IIS _) IIZ fsum =
  case decompIdx_4 r n fsum of
    Right x -> FInL x
    Left x -> x
fuseSumW4 (RemS _) (IIS _) (IIS _) (FInL x) = FInL x
fuseSumW4 (RemS r) (IIS n) (IIS m) (FInR x) = FInR (fuseSumW3 r n m x)

fuseSumW5 ::
     (n == m) ~ 'False
  => RemoveW n '[ f0, f1, f2, f3, f4] fs
  -> IIndex n '[ f0, f1, f2, f3, f4] f
  -> IIndex m '[ f0, f1, f2, f3, f4] f
  -> FSum '[ f0, f1, f2, f3, f4] a
  -> FSum fs a
{-# INLINE fuseSumW5 #-}
fuseSumW5 RemZ IIZ (IIS m) (FInL x) = inject4 m x
fuseSumW5 RemZ IIZ (IIS _) (FInR x) = x
fuseSumW5 r@(RemS _) n@(IIS _) IIZ fsum =
  case decompIdx_5 r n fsum of
    Right x -> FInL x
    Left x -> x
fuseSumW5 (RemS _) (IIS _) (IIS _) (FInL x) = FInL x
fuseSumW5 (RemS r) (IIS n) (IIS m) (FInR x) = FInR (fuseSumW4 r n m x)

fuseSumW6 ::
     (n == m) ~ 'False
  => RemoveW n '[ f0, f1, f2, f3, f4, f5] fs
  -> IIndex n '[ f0, f1, f2, f3, f4, f5] f
  -> IIndex m '[ f0, f1, f2, f3, f4, f5] f
  -> FSum '[ f0, f1, f2, f3, f4, f5] a
  -> FSum fs a
{-# INLINE fuseSumW6 #-}
fuseSumW6 RemZ IIZ (IIS m) (FInL x) = inject5 m x
fuseSumW6 RemZ IIZ (IIS _) (FInR x) = x
fuseSumW6 r@(RemS _) n@(IIS _) IIZ fsum =
  case decompIdx_6 r n fsum of
    Right x -> FInL x
    Left x -> x
fuseSumW6 (RemS _) (IIS _) (IIS _) (FInL x) = FInL x
fuseSumW6 (RemS r) (IIS n) (IIS m) (FInR x) = FInR (fuseSumW5 r n m x)

-- | Unify two terms in the sum by transforming them into a common
-- functor, discarding the first term and replacing the second.
--
-- Specialised to different indices, the type looks like this:
--
-- @
-- \\f g -> 'fuseSumWith' f g i0 i1
--   :: (f0 a -> h a) -> (f1 a -> h a) -> 'FSum' (f0 : f1 : fs) a -> 'FSum' (h : as) a
--
-- \\f g -> 'fuseSumWith' f g i0 i2
--   :: (f0 a -> h a) -> (f2 a -> h a) -> 'FSum' (f0 : f1 : f2 : fs) a -> 'FSum' (f1 : h : fs) a
--
-- \\f g -> 'fuseSumWith' f g i2 i0
--   :: (f2 a -> h a) -> (f0 a -> h a) -> 'FSum' (f0 : f1 : f2 : fs) a -> 'FSum' (h : f1 : fs) a
-- @
fuseSumWith ::
     forall n m f g h a fs fsrep res.
     ((n == m) ~ 'False, Replace m fs h fsrep, Remove n fsrep res)
  => (f a -> h a) -- ^ Transform first fused element.
  -> (g a -> h a) -- ^ Transform second fused element.
  -> IIndex n fs f -- ^ Index of removed element.
  -> IIndex m fs g -- ^ Index of replaced element.
  -> FSum fs a
  -> FSum res a
{-# INLINE fuseSumWith #-}
fuseSumWith f g n' = fuseSumWithW f g removeW n' replaceW

fuseSumWithW ::
     forall n m f g h a fs fsrep res. (n == m) ~ 'False
  => (f a -> h a)
  -> (g a -> h a)
  -> RemoveW n fsrep res
  -> IIndex n fs f
  -> ReplaceW m fs h fsrep
  -> IIndex m fs g
  -> FSum fs a
  -> FSum res a
{-# NOINLINE[0] fuseSumWithW #-}
fuseSumWithW f g = loop
  where
    loop ::
         forall n' m' fs' fs'' res'. (n' == m') ~ 'False
      => RemoveW n' fs'' res'
      -> IIndex n' fs' f
      -> ReplaceW m' fs' h fs''
      -> IIndex m' fs' g
      -> FSum fs' a
      -> FSum res' a
    loop RemZ IIZ (RepS rep) (IIS m) (FInL x) =
      finjectIdx (replaceIdx m \\ rep) (f x)
    loop RemZ IIZ (RepS rep) (IIS m) (FInR y) = freplaceIdx m g y \\ rep
    loop (RemS _) (IIS _) RepZ IIZ (FInL x) = FInL (g x)
    loop (RemS r) (IIS n) RepZ IIZ (FInR y) =
      case fdecompIdx n y \\ r of
        Right x -> FInL (f x)
        Left other -> FInR other
    loop (RemS _) (IIS _) (RepS _) (IIS _) (FInL x) = FInL x
    loop (RemS r) (IIS n) (RepS rep) (IIS m) (FInR y) = FInR (loop r n rep m y)

{-# RULES
"fsum/fuseSumWith/2" fuseSumWithW = fuseSumWithW2
"fsum/fuseSumWith/3" fuseSumWithW = fuseSumWithW3
"fsum/fuseSumWith/4" fuseSumWithW = fuseSumWithW4
"fsum/fuseSumWith/5" fuseSumWithW = fuseSumWithW5
"fsum/fuseSumWith/6" fuseSumWithW = fuseSumWithW6
 #-}

fuseSumWithW2 ::
     (n == m) ~ 'False
  => (f a -> h a)
  -> (g a -> h a)
  -> RemoveW n fsrep res
  -> IIndex n '[ f0, f1] f
  -> ReplaceW m '[ f0, f1] h fsrep
  -> IIndex m '[ f0, f1] g
  -> FSum '[ f0, f1] a
  -> FSum res a
{-# INLINE fuseSumWithW2 #-}
fuseSumWithW2 f _ RemZ IIZ (RepS RepZ) (IIS IIZ) (FInL x) = FInL (f x)
fuseSumWithW2 _ g RemZ IIZ (RepS RepZ) (IIS IIZ) (FInR x) =
  FInL (g (fsumOnly x))
fuseSumWithW2 _ g (RemS RemZ) (IIS IIZ) RepZ IIZ (FInL x) = FInL (g x)
fuseSumWithW2 f _ (RemS RemZ) (IIS IIZ) RepZ IIZ (FInR x) =
  FInL (f (fsumOnly x))
fuseSumWithW2 _ _ _ (IIS (IIS n)) _ _ _ = absurdIdx n
fuseSumWithW2 _ _ _ _ (RepS (RepS r)) _ _ = absurdReplace r

fuseSumWithW3 ::
     (n == m) ~ 'False
  => (f a -> h a)
  -> (g a -> h a)
  -> RemoveW n fsrep res
  -> IIndex n '[ f0, f1, f2] f
  -> ReplaceW m '[ f0, f1, f2] h fsrep
  -> IIndex m '[ f0, f1, f2] g
  -> FSum '[ f0, f1, f2] a
  -> FSum res a
{-# INLINE fuseSumWithW3 #-}
fuseSumWithW3 f _ RemZ IIZ (RepS rep) (IIS _) (FInL x) =
  finjectIdx (replaceIdxW rep) (f x)
fuseSumWithW3 _ g RemZ IIZ (RepS rep) (IIS m) (FInR x) = freplaceIdxW rep m g x
fuseSumWithW3 _ g (RemS _) (IIS _) RepZ IIZ (FInL x) = FInL (g x)
fuseSumWithW3 f _ (RemS r) (IIS n) RepZ IIZ (FInR y) =
  case fdecompIdx_W r n y of
    Right x -> FInL (f x)
    Left other -> FInR other
fuseSumWithW3 _ _ (RemS _) (IIS _) (RepS _) (IIS _) (FInL x) = FInL x
fuseSumWithW3 f g (RemS r) (IIS n) (RepS rep) (IIS m) (FInR x) =
  FInR (fuseSumWithW2 f g r n rep m x)

fuseSumWithW4 ::
     (n == m) ~ 'False
  => (f a -> h a)
  -> (g a -> h a)
  -> RemoveW n fsrep res
  -> IIndex n '[ f0, f1, f2, f3] f
  -> ReplaceW m '[ f0, f1, f2, f3] h fsrep
  -> IIndex m '[ f0, f1, f2, f3] g
  -> FSum '[ f0, f1, f2, f3] a
  -> FSum res a
{-# INLINE fuseSumWithW4 #-}
fuseSumWithW4 f _ RemZ IIZ (RepS rep) (IIS _) (FInL x) =
  finjectIdx (replaceIdxW rep) (f x)
fuseSumWithW4 _ g RemZ IIZ (RepS rep) (IIS m) (FInR x) = freplaceIdxW rep m g x
fuseSumWithW4 _ g (RemS _) (IIS _) RepZ IIZ (FInL x) = FInL (g x)
fuseSumWithW4 f _ (RemS r) (IIS n) RepZ IIZ (FInR y) =
  case fdecompIdx_W r n y of
    Right x -> FInL (f x)
    Left other -> FInR other
fuseSumWithW4 _ _ (RemS _) (IIS _) (RepS _) (IIS _) (FInL x) = FInL x
fuseSumWithW4 f g (RemS r) (IIS n) (RepS rep) (IIS m) (FInR x) =
  FInR (fuseSumWithW3 f g r n rep m x)

fuseSumWithW5 ::
     (n == m) ~ 'False
  => (f a -> h a)
  -> (g a -> h a)
  -> RemoveW n fsrep res
  -> IIndex n '[ f0, f1, f2, f3, f4] f
  -> ReplaceW m '[ f0, f1, f2, f3, f4] h fsrep
  -> IIndex m '[ f0, f1, f2, f3, f4] g
  -> FSum '[ f0, f1, f2, f3, f4] a
  -> FSum res a
{-# INLINE fuseSumWithW5 #-}
fuseSumWithW5 f _ RemZ IIZ (RepS rep) (IIS _) (FInL x) =
  finjectIdx (replaceIdxW rep) (f x)
fuseSumWithW5 _ g RemZ IIZ (RepS rep) (IIS m) (FInR x) = freplaceIdxW rep m g x
fuseSumWithW5 _ g (RemS _) (IIS _) RepZ IIZ (FInL x) = FInL (g x)
fuseSumWithW5 f _ (RemS r) (IIS n) RepZ IIZ (FInR y) =
  case fdecompIdx_W r n y of
    Right x -> FInL (f x)
    Left other -> FInR other
fuseSumWithW5 _ _ (RemS _) (IIS _) (RepS _) (IIS _) (FInL x) = FInL x
fuseSumWithW5 f g (RemS r) (IIS n) (RepS rep) (IIS m) (FInR x) =
  FInR (fuseSumWithW4 f g r n rep m x)

fuseSumWithW6 ::
     (n == m) ~ 'False
  => (f a -> h a)
  -> (g a -> h a)
  -> RemoveW n fsrep res
  -> IIndex n '[ f0, f1, f2, f3, f4, f5] f
  -> ReplaceW m '[ f0, f1, f2, f3, f4, f5] h fsrep
  -> IIndex m '[ f0, f1, f2, f3, f4, f5] g
  -> FSum '[ f0, f1, f2, f3, f4, f5] a
  -> FSum res a
{-# INLINE fuseSumWithW6 #-}
fuseSumWithW6 f _ RemZ IIZ (RepS rep) (IIS _) (FInL x) =
  finjectIdx (replaceIdxW rep) (f x)
fuseSumWithW6 _ g RemZ IIZ (RepS rep) (IIS m) (FInR x) = freplaceIdxW rep m g x
fuseSumWithW6 _ g (RemS _) (IIS _) RepZ IIZ (FInL x) = FInL (g x)
fuseSumWithW6 f _ (RemS r) (IIS n) RepZ IIZ (FInR y) =
  case fdecompIdx_W r n y of
    Right x -> FInL (f x)
    Left other -> FInR other
fuseSumWithW6 _ _ (RemS _) (IIS _) (RepS _) (IIS _) (FInL x) = FInL x
fuseSumWithW6 f g (RemS r) (IIS n) (RepS rep) (IIS m) (FInR x) =
  FInR (fuseSumWithW5 f g r n rep m x)

-- | Unify /all/ of the terms in the sum, if they are all identical
-- (which is the meaning of a rather weird-looking constraint).
fuseSumAll :: All (Known ((:~:) f)) fs => FSum fs a -> f a
{-# NOINLINE[0] fuseSumAll #-}
fuseSumAll (FInL f) = idEq f
fuseSumAll (FInR fs) = fuseSumAll fs

{-# RULES
"fsum/fuseSumAll/0" fuseSumAll = fuseSumAll0
"fsum/fuseSumAll/1" fuseSumAll = fuseSumAll1
"fsum/fuseSumAll/2" fuseSumAll = fuseSumAll2
"fsum/fuseSumAll/3" fuseSumAll = fuseSumAll3
"fsum/fuseSumAll/4" fuseSumAll = fuseSumAll4
"fsum/fuseSumAll/5" fuseSumAll = fuseSumAll5
"fsum/fuseSumAll/6" fuseSumAll = fuseSumAll6
 #-}

fuseSumAll0 :: FSum '[] a -> f a
{-# INLINE fuseSumAll0 #-}
fuseSumAll0 = absurdFSum

fuseSumAll1 :: FSum '[ f] a -> f a
{-# INLINE fuseSumAll1 #-}
fuseSumAll1 = fsumOnly

fuseSumAll2 :: FSum '[ f, f] a -> f a
{-# INLINE fuseSumAll2 #-}
fuseSumAll2 (FInL x) = x
fuseSumAll2 (FInR x) = fuseSumAll1 x

fuseSumAll3 :: FSum '[ f, f, f] a -> f a
{-# INLINE fuseSumAll3 #-}
fuseSumAll3 (FInL x) = x
fuseSumAll3 (FInR x) = fuseSumAll2 x

fuseSumAll4 :: FSum '[ f, f, f, f] a -> f a
{-# INLINE fuseSumAll4 #-}
fuseSumAll4 (FInL x) = x
fuseSumAll4 (FInR x) = fuseSumAll3 x

fuseSumAll5 :: FSum '[ f, f, f, f, f] a -> f a
{-# INLINE fuseSumAll5 #-}
fuseSumAll5 (FInL x) = x
fuseSumAll5 (FInR x) = fuseSumAll4 x

fuseSumAll6 :: FSum '[ f, f, f, f, f, f] a -> f a
{-# INLINE fuseSumAll6 #-}
fuseSumAll6 (FInL x) = x
fuseSumAll6 (FInR x) = fuseSumAll5 x

idEq ::
  forall f g a. Known ((:~:) f) g
  => g a
  -> f a
idEq g = g \\ (known :: f :~: g)

-- | An analogue of 'all' for type-level lists.
--
-- Constraint @'All' f as@ means that all elements of the type-level
-- list @as@ should satisfy the constraint @f@; e.g. @'All' 'Functor'
-- fs@ means that all elements of @fs@ should be functors.
type All f as = ListC (f <$> as)
