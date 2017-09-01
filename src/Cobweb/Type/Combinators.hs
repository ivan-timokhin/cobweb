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
{-# LANGUAGE FunctionalDependencies #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE PolyKinds #-}
{-# LANGUAGE ScopedTypeVariables #-}
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
  , IRemove(IRemZ, IRemS)
  , IWithout(iwithout)
    -- * Replacing elements
  , IReplace(IRepZ, IRepS)
  , IReplaced(ireplace)
  , replaceIdx
    -- * Manipulating 'FSum'
  , fdecompIdx
  , fdecompReplaceIdx
  , freplaceIdx
  , finjectIdx
  , finl
  , finr
  , fuse
    -- * Type synonyms
  , All
  ) where

import Data.Bifunctor (first)
import Data.Type.Index (Index(IS, IZ))
import Data.Type.Length (Length(LS, LZ))
import Data.Type.Sum.Lifted (FSum(FInL, FInR), injectFSum)
import Type.Class.Known (Known(known))
import Type.Class.Witness (Witness((\\)))
import Type.Family.Constraint (ØC)
import Type.Family.List (type (++), type (<$>), Last, ListC, Null)
import Type.Family.Nat
       (Len, N(S, Z), N0, N1, N10, N2, N3, N4, N5, N6, N7, N8, N9, NatEq,
        Pred)

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

-- | A value of a type @'IRemove' n as bs@ witnesses that @as@ has
-- @n@th element, and removing it yields @bs@.
--
-- Examples:
--
-- @
-- 'IRemZ' :: 'IRemove' 'N0' (a0 : as) as
-- 'IRemS' 'IRemZ' :: 'IRemove' 'N1' (a0 : a1 : as) (a0 : as)
-- 'IRemS' ('IRemS' 'IRemZ') :: 'IRemove' 'N2' (a0 : a1 : a2 : as) (a0 : a1 : as)
-- @
--
-- And so on.
data IRemove :: N -> [k] -> [k] -> * where
  -- | Remove the head
  IRemZ :: IRemove 'Z (a : as) as
  -- | Remove some element in the tail
  IRemS :: !(IRemove n as bs) -> IRemove ('S n) (a : as) (a : bs)

-- | Signifies that the list @as@ has @n@th element, and removing it
-- yields @bs@.
--
-- Real instances of this class are defined inductively, but it can be
-- thought of as having the following instances:
--
-- @
-- instance 'IWithout' 'N0' (a0 : as) as
-- instance 'IWithout' 'N1' (a0 : a1 : as) (a0 : as)
-- instance 'IWithout' 'N2' (a0 : a1 : a2 : as) (a0 : a1 : as)
-- @
--
-- And so on.
--
-- Because of the functional dependency, this class can be used (and
-- often is) to introduce @bs@ if @n@ and @as@ are known from some
-- other source (such as 'IIndex').
--
-- This class is a constraint-level equivalent of 'IRemove';
-- conversion goes both ways, through 'iwithout' in one direction and
-- 'Witness' instance in the other.
class IWithout (n :: N) (as :: [k]) (bs :: [k]) | n as -> bs where
  -- | A witness of the relationship in question.
  iwithout :: IRemove n as bs

instance IWithout 'Z (a : as) as where
  iwithout = IRemZ

instance IWithout n as bs => IWithout ('S n) (a : as) (a : bs) where
  iwithout = IRemS iwithout

instance Witness ØC (IWithout n as bs) (IRemove n as bs) where
  f \\ IRemZ = f
  f \\ IRemS r = f \\ r

-- | A value of type @'IReplace' n as b bs@ witnesses that the list
-- @as@ has @n@th element, and replacing it with @b@ yields @bs@.
--
-- Examples:
--
-- @
-- 'IRepZ' :: 'IReplace' 'N0' (a0 : as) b (b : as)
-- 'IRepS' 'IRepZ' :: 'IReplace' 'N1' (a0 : a1 : as) (a0 : b : as)
-- 'IRepS' ('IRepS' 'IRepZ') :: 'IReplace' 'N2' (a0 : a1 : a2 : as) (a0 : a1 : b : as)
-- @
--
-- And so on.
data IReplace :: N -> [k] -> k -> [k] -> * where
  -- | Replace the head
  IRepZ :: IReplace 'Z (a : as) b (b : as)
  -- | Replace some element in the tail
  IRepS :: !(IReplace n as b bs) -> IReplace ('S n) (a : as) b (a : bs)

-- | Signifies that the list @as@ has @n@th element, and replacing it
-- with @b@ yields list @bs@.
--
-- Real instances of the class are defined inductively, but it can be
-- thought of as having the following instances:
--
-- @
-- instance 'IReplaced' 'N0' (a : as) b (b : as)
-- instance 'IReplaced' 'N1' (a0 : a1 : as) b (a0 : b : as)
-- instance 'IReplaced' 'N2' (a0 : a1 : a2 : as) b (a0 : a1 : b : as)
-- @
--
-- And so on.
--
-- Because of the functional dependency, this class is typically used
-- to /introduce/ type bs in the context where all other parameters
-- are known.
--
-- This is a constraint-level equivalent of 'IReplace'; the conversion
-- goes both ways, through 'ireplace' in one direction and 'Witness'
-- instance in another.
class IReplaced n as b bs | n as b -> bs where
  -- | Witness of the relationship in question
  ireplace :: IReplace n as b bs

instance IReplaced 'Z (a : as) b (b : as) where
  ireplace = IRepZ

instance IReplaced n as b bs => IReplaced ('S n) (a : as) b (a : bs) where
  ireplace = IRepS ireplace

instance Witness ØC (IReplaced n as b bs) (IReplace n as b bs) where
  f \\ IRepZ = f
  f \\ IRepS r = f \\ r

-- | Produce an index of a replaced element in the new list.
replaceIdx :: IReplace n as b bs -> IIndex n bs b
replaceIdx IRepZ = IIZ
replaceIdx (IRepS r) = IIS (replaceIdx r)

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
     IWithout n fs gs
  => IIndex n fs f -- ^ An index of an element to be extracted
  -> FSum fs a -- ^ A sum which may or may not be represented by the
     -- element in question
  -> Either (FSum gs a) (f a) -- ^ Either the requested element, or
     -- some other one.
fdecompIdx = loop iwithout
  where
    loop ::
         IRemove n fs gs
      -> IIndex n fs f
      -> FSum fs a
      -> Either (FSum gs a) (f a)
    loop _ IIZ (FInL f) = Right f
    loop IRemZ IIZ (FInR g) = Left g
    loop (IRemS _) (IIS _) (FInL g) = Left (FInL g)
    loop (IRemS r) (IIS n) (FInR fs) = first FInR (loop r n fs)

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
     IReplaced n fs g gs
  => IIndex n fs f
  -> p g
  -> FSum fs a
  -> Either (FSum gs a) (f a)
fdecompReplaceIdx = loop ireplace
  where
    loop ::
         IReplace n fs g gs
      -> IIndex n fs f
      -> p g
      -> FSum fs a
      -> Either (FSum gs a) (f a)
    loop _ IIZ _ (FInL f) = Right f
    loop IRepZ IIZ _ (FInR g) = Left (FInR g)
    loop (IRepS _) (IIS _) _ (FInL g) = Left (FInL g)
    loop (IRepS r) (IIS n) p (FInR fs) = first FInR (loop r n p fs)

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
     IReplaced n fs g gs
  => IIndex n fs f -- ^ An index of a functor to be replaced.
  -> (f a -> g a) -- ^ A function used to transform old functor into a
     -- new one.
  -> FSum fs a -- ^ An old sum, which may or may not be represented by
     -- the functor in question.
  -> FSum gs a -- ^ Resulting sum.
freplaceIdx = loop ireplace
  where
    loop ::
         IReplace n fs g gs
      -> IIndex n fs f
      -> (f a -> g a)
      -> FSum fs a
      -> FSum gs a
    loop IRepZ IIZ h (FInL f) = FInL (h f)
    loop IRepZ IIZ _ (FInR g) = FInR g
    loop (IRepS _) (IIS _) _ (FInL g) = FInL g
    loop (IRepS r) (IIS n) h (FInR fs) = FInR (loop r n h fs)

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
--
-- Since the value of the index @n@ is not used at type level, this is just
--
-- @
-- 'finjectIdx' = 'injectFSum' . 'forgetIdx'
-- @
finjectIdx ::
     IIndex n fs f -- ^ An index at which to inject the functor.
  -> f a -- ^ The value to be injected.
  -> FSum fs a -- ^ A sum represented by the provided value at the
     -- provided index.
finjectIdx = injectFSum . forgetIdx

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
-- (hence @'NatEq' n m ~ ''False'@ constraint).
--
-- Specialised to different values of the indices, the type looks like
-- this:
--
-- @
-- 'fuse' 'i0' 'i1' :: 'FSum' (f : f : fs) a -> 'FSum' (f : fs) a
-- 'fuse' 'i0' 'i2' :: 'FSum' (f : f1 : f : fs) a -> 'FSum' (f1 : f : fs)
-- 'fuse' 'i2' 'i0' :: 'FSum' (f : f1 : f : fs) a -> 'FSum' (f : f1 : fs)
-- @
--
-- Trying to call @'fuse' 'i0' 'i0'@ and such results in a type
-- error.  Unfortunately, it does not mention indices at all, instead
-- complaining that
--
-- >    • Couldn't match type ‘'True’ with ‘'False’
-- >        arising from a use of ‘fuse’
--
-- so if such errors arise, a likely cause is trying to 'fuse' a term
-- with itself.
fuse ::
     forall n m fs gs f a. (IWithout n fs gs, NatEq n m ~ 'False)
  => IIndex n fs f
  -> IIndex m fs f
  -> FSum fs a
  -> FSum gs a
fuse = loop (iwithout :: IRemove n fs gs)
  where
    loop ::
         (NatEq n' m' ~ 'False)
      => IRemove n' fs' gs'
      -> IIndex n' fs' f
      -> IIndex m' fs' f
      -> FSum fs' a
      -> FSum gs' a
    loop IRemZ IIZ (IIS m) (FInL f) = finjectIdx m f
    loop IRemZ IIZ (IIS _) (FInR other) = other
    loop r@(IRemS _) n@(IIS _) IIZ fsum =
      case fdecompIdx n fsum \\ r of
        Right f -> FInL f
        Left other -> other
    loop (IRemS _) (IIS _) (IIS _) (FInL f) = FInL f
    loop (IRemS r) (IIS n) (IIS m) (FInR other) = FInR (loop r n m other)

-- | An analogue of 'all' for type-level lists.
--
-- Constraint @'All' f as@ means that all elements of the type-level
-- list @as@ should satisfy the constraint @f@; e.g. @'All' 'Functor'
-- fs@ means that all elements of @fs@ should be functors.
type All f as = ListC (f <$> as)
