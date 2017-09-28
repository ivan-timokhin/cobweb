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

{-# RULES
"fsum/fmap1" map_ = map1_
"fsum/fmap2" map_ = map2_
"fsum/fmap3" map_ = map3_
"fsum/fmap4" map_ = map4_
"fsum/fmap5" map_ = map5_
 #-}

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
{-# NOINLINE lastIndex #-}
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
 #-}

lastIndex1 :: IIndex N0 '[a] a
{-# INLINE lastIndex1 #-}
lastIndex1 = IIZ

lastIndex2 :: IIndex N1 '[a, b] b
{-# INLINE lastIndex2 #-}
lastIndex2 = IIS IIZ

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
replaceIdx :: Replace n as b bs => IIndex n as a -> IIndex n bs b
replaceIdx = loop replaceW
  where
    loop :: ReplaceW n as b bs -> IIndex n as a -> IIndex n bs b
    loop RepZ IIZ = IIZ
    loop (RepS r) (IIS idx) = IIS (loop r idx)

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
decompIdx_1 (RemS r) (IIS _) _ = case r of {}

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
     Replace n fs g gs
  => IIndex n fs f
  -> p g
  -> FSum fs a
  -> Either (FSum gs a) (f a)
fdecompReplaceIdx = loop replaceW
  where
    loop ::
         ReplaceW n fs g gs
      -> IIndex n fs f
      -> p g
      -> FSum fs a
      -> Either (FSum gs a) (f a)
    loop RepZ IIZ _ (FInL x) = Right x
    loop RepZ IIZ _ (FInR x) = Left (FInR x)
    loop (RepS _) (IIS _) _ (FInL x) = Left (FInL x)
    loop (RepS r) (IIS n) p (FInR x) = first FInR (loop r n p x)

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
freplaceIdx n f = loop replaceW n
  where
    loop :: ReplaceW n' fs' g gs' -> IIndex n' fs' f -> FSum fs' a -> FSum gs' a
    loop RepZ IIZ (FInL x) = FInL (f x)
    loop RepZ IIZ (FInR x) = FInR x
    loop (RepS _) (IIS _) (FInL x) = FInL x
    loop (RepS r) (IIS n') (FInR x) = FInR (loop r n' x)

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
{-# NOINLINE finjectIdx #-}
finjectIdx n f = loop n
  where
    loop :: IIndex n' fs' f -> FSum fs' a
    loop IIZ = FInL f
    loop (IIS n') = FInR (loop n')

{-# RULES
"finjectIdx/1" finjectIdx = inject1
"finjectIdx/2" finjectIdx = inject2
 #-}

inject1 :: IIndex n '[f0] f -> f a -> FSum '[f0] a
{-# INLINE inject1 #-}
inject1 IIZ = FInL
inject1 (IIS n) = case n of {}

inject2 :: IIndex n '[f0, f1] f -> f a -> FSum '[f0, f1] a
{-# INLINE inject2 #-}
inject2 IIZ = FInL
inject2 (IIS n) = FInR . inject1 n

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
 #-}

finl0 :: proxy gs -> FSum '[] a -> FSum gs a
{-# INLINE finl0 #-}
finl0 _ = absurdFSum

finl1 :: proxy gs -> FSum '[f0] a -> FSum (f0 : gs) a
{-# INLINE finl1 #-}
finl1 _ (FInL x) = FInL x
finl1 p (FInR x) = FInR (finl0 p x)

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
fuseSum = loop removeW
  where
    loop ::
         (n == m) ~ 'False
      => RemoveW n fs fs'
      -> IIndex n fs f
      -> IIndex m fs f
      -> FSum fs a
      -> FSum fs' a
    loop RemZ IIZ (IIS m) (FInL x) = finjectIdx m x
    loop RemZ IIZ (IIS _) (FInR y) = y
    loop r@(RemS _) n@(IIS _) IIZ fsum =
      case fdecompIdx n fsum \\ r of
        Right x -> FInL x
        Left y -> y
    loop (RemS _) (IIS _) (IIS _) (FInL x) = FInL x
    loop (RemS r) (IIS n) (IIS m) (FInR y) = FInR (loop r n m y)

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
fuseSumWith f g n' = loop removeW n' replaceW
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

-- | Unify /all/ of the terms in the sum, if they are all identical
-- (which is the meaning of a rather weird-looking constraint).
fuseSumAll :: All (Known ((:~:) f)) fs => FSum fs a -> f a
fuseSumAll (FInL f) = idEq f
fuseSumAll (FInR fs) = fuseSumAll fs

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
