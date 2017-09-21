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
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE PolyKinds #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE UndecidableInstances #-}

module Cobweb.Type.Combinators
  (
    -- * Indices
    IIndex(IIZ, IIS)
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
  , Remove
    -- * Replacing elements
  , Replace
  , replaceIdx
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
import Data.Type.Sum.Lifted (FSum(FInL, FInR), injectFSum, nilFSum)
import Data.Void (absurd)
import Type.Class.Known (Known(known))
import Type.Class.Witness (Witness((\\)))
import Type.Family.List (type (++), type (<$>), Last, ListC, Null)
import Type.Family.Nat
       (Len, N(S, Z), N0, N1, N10, N2, N3, N4, N5, N6, N7, N8, N9, Pred)

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
lastIndex = loop (known :: Length as)
  where
    loop ::
         (Null as' ~ 'False)
      => Length as'
      -> IIndex (Pred (Len as')) as' (Last as')
    loop (LS LZ) = IIZ
    loop (LS n@(LS _)) = IIS (loop n)

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

type family Remove (n :: N) (as :: [k]) where
  Remove n '[] = '[]
  Remove 'Z (a : as) = as
  Remove ('S n) (a : as) = a : Remove n as

type family Replace (n :: N) (as :: [k]) (a :: k) where
  Replace n '[] a = '[]
  Replace 'Z (a : as) b = b : as
  Replace ('S n) (a : as) b = a : Replace n as b

-- | Produce an index of a replaced element in the new list.
replaceIdx :: IIndex n as a -> IIndex n (Replace n as b) b
replaceIdx IIZ = IIZ
replaceIdx (IIS n) = IIS (replaceIdx n)

-- | Extract the only term of a single-term sum.
fsumOnly :: FSum '[f] a -> f a
fsumOnly (FInL f) = f
fsumOnly (FInR f) = absurd . nilFSum $ f

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
     IIndex n fs f -- ^ An index of an element to be extracted
  -> FSum fs a
  -> Either (FSum (Remove n fs) a) (f a)
fdecompIdx IIZ (FInL x) = Right x
fdecompIdx IIZ (FInR x) = Left x
fdecompIdx (IIS _) (FInL x) = Left (FInL x)
fdecompIdx (IIS n) (FInR x) = first FInR (fdecompIdx n x)

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
     IIndex n fs f -> p g -> FSum fs a -> Either (FSum (Replace n fs g) a) (f a)
fdecompReplaceIdx IIZ _ (FInL x) = Right x
fdecompReplaceIdx IIZ _ (FInR x) = Left (FInR x)
fdecompReplaceIdx (IIS _) _ (FInL x) = Left (FInL x)
fdecompReplaceIdx (IIS n) p (FInR x) = first FInR (fdecompReplaceIdx n p x)

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
     IIndex n fs f -- ^ An index of a functor to be replaced.
  -> (f a -> g a) -- ^ A function used to transform old functor into a
     -- new one.
  -> FSum fs a -- ^ An old sum, which may or may not be represented by
     -- the functor in question.
  -> FSum (Replace n fs g) a
freplaceIdx IIZ f (FInL x) = FInL (f x)
freplaceIdx IIZ _ (FInR x) = FInR x
freplaceIdx (IIS _) _ (FInL x) = FInL x
freplaceIdx (IIS n) f (FInR x) = FInR (freplaceIdx n f x)

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
{-# INLINE[0] finjectIdx #-}
finjectIdx n f = loop n
  where
    loop :: IIndex n' fs' f -> FSum fs' a
    loop IIZ = FInL f
    loop (IIS n') = FInR (loop n')

{-# RULES
"finjectIdx/IIZ" forall f (n :: IIndex N0 (f : fs) f) .
                 finjectIdx n f = FInL f
"finjectIdx/IIS" forall f n. finjectIdx n f = finjectIdxSucc n f
 #-}

finjectIdxSucc :: IIndex ('S n) (g : fs) f -> f a -> FSum (g : fs) a
{-# INLINE finjectIdxSucc #-}
finjectIdxSucc (IIS n) f = FInR (finjectIdx n f)

-- | Embed a sum into a sum of a larger list, obtained by adding
-- elements on the right.
--
-- This function does not, in a sense, change the /value/ stored, only
-- its /type/.
--
-- Since the 'Type.Family.List.++' type family is not injective, a
-- proxy argument is used to guide type inference.
finl :: proxy gs -> FSum fs a -> FSum (fs ++ gs) a
finl _ (FInL f) = FInL f
finl proxy (FInR f) = FInR (finl proxy f)

-- | Embed a sum into a sum of a larger list, obtained by adding
-- elements of the left.
--
-- This function is similar to 'finl', but, due to right-recursive
-- nature of the 'FSum' definition, requires a @'Known' 'Length'@
-- constraint on the left list.
finr ::
     forall proxy fs gs a. Known Length fs
  => proxy fs
  -> FSum gs a
  -> FSum (fs ++ gs) a
finr _ = loop (known :: Length fs)
  where
    loop :: Length fs' -> FSum gs a -> FSum (fs' ++ gs) a
    loop LZ = id
    loop (LS n) = FInR . loop n

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
     ((n == m) ~ 'False)
  => IIndex n fs f -- ^ The index of the term to be moved.
  -> IIndex m fs f -- ^ The index of the term to be kept.
  -> FSum fs a
  -> FSum (Remove n fs) a
fuseSum IIZ (IIS m) (FInL x) = finjectIdx m x
fuseSum IIZ (IIS _) (FInR y) = y
fuseSum n@(IIS _) IIZ fsum =
  case fdecompIdx n fsum of
    Right x -> FInL x
    Left y -> y
fuseSum (IIS _) (IIS _) (FInL x) = FInL x
fuseSum (IIS n) (IIS m) (FInR y) = FInR (fuseSum n m y)

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
     forall n m f g h a fs. ((n == m) ~ 'False)
  => (f a -> h a) -- ^ Transform first fused element.
  -> (g a -> h a) -- ^ Transform second fused element.
  -> IIndex n fs f -- ^ Index of removed element.
  -> IIndex m fs g -- ^ Index of replaced element.
  -> FSum fs a
  -> FSum (Remove n (Replace m fs h)) a
fuseSumWith f g = loop
  where
    loop ::
         forall n' m' fs'. (n' == m') ~ 'False
      => IIndex n' fs' f
      -> IIndex m' fs' g
      -> FSum fs' a
      -> FSum (Remove n' (Replace m' fs' h)) a
    loop IIZ (IIS m) (FInL x) = finjectIdx (replaceIdx m) (f x)
    loop IIZ (IIS m) (FInR y) = freplaceIdx m g y
    loop (IIS _) IIZ (FInL x) = FInL (g x)
    loop (IIS n) IIZ (FInR y) =
      case fdecompIdx n y of
        Right x -> FInL (f x)
        Left other -> FInR other
    loop (IIS _) (IIS _) (FInL x) = FInL x
    loop (IIS n) (IIS m) (FInR y) = FInR (loop n m y)

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
