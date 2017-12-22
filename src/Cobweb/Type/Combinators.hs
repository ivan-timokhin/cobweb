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
  , Inductive
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
  , AllEqual
  ) where

import Data.Bifunctor (first)
import Data.Kind (Constraint)
import Data.Type.Equality ((:~:)(Refl), type (==))
import Data.Type.Index (Index(IS, IZ))
import Data.Type.Length (Length(LS, LZ))
import Type.Family.List (Last, Null)
import Type.Family.Nat
  ( Len
  , N(S, Z)
  , N0
  , N1
  , N10
  , N2
  , N3
  , N4
  , N5
  , N6
  , N7
  , N8
  , N9
  , Pred
  )

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
lastIndex ::
     forall as. (Inductive as, Null as ~ 'False)
  => IIndex (Pred (Len as)) as (Last as)
{-# INLINE lastIndex #-}
lastIndex =
  case lastIdxI (lengthI :: Length as) of
    Left r -> case r of {}
    Right i -> i

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
class (Inductive as, Inductive bs) =>
      Remove n as bs
  | n as -> bs
  where
  -- | Witness of the relationship in question.
  removeW :: RemoveW n as bs

instance Inductive as => Remove 'Z (a : as) as where
  removeW = RemZ

instance Remove n as bs => Remove ('S n) (a : as) (a : bs) where
  removeW = RemS removeW

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
class (Inductive as, Inductive bs) =>
      Replace n as b bs
  | n as b -> bs
  where
  -- | Witness of the relationship in question.
  replaceW :: ReplaceW n as b bs

instance Inductive as => Replace 'Z (a : as) b (b : as) where
  replaceW = RepZ

instance Replace n as b bs => Replace ('S n) (a : as) b (a : bs) where
  replaceW = RepS replaceW

-- | Witnesses that @cs@ is @as@ and @bs@ concatenated (in value-level
-- lingo, @cs = as ++ bs@).
data AppendW (as :: [k]) (bs :: [k]) (cs :: [k]) where
  -- | Prepend and empty list.
  AppZ :: AppendW '[] as as
  -- | Prepend a non-empty list.
  AppS :: !(AppendW as bs cs) -> AppendW (a : as) bs (a : cs)

-- | A class used to introduce (via functional dependency) @cs@ as
-- @bs@ appended to @as@ (in value-level lingo, @cs = as ++ bs@).
class (Inductive as, Inductive bs, Inductive cs) =>
      Append as bs cs
  | as bs -> cs
  , as cs -> bs
  where
  -- | Witness of the relationship in question.
  appendW :: AppendW as bs cs

instance Inductive as => Append '[] as as where
  appendW = AppZ

instance Append as bs cs => Append (a : as) bs (a : cs) where
  appendW = AppS appendW

-- | This is a utility class, used to unroll operations on 'FSum',
-- significantly speeding them up in the common case of short known
-- list.  All finite lists are instances of this class, so it doesn't
-- actually constrain anything.
class Inductive (fs :: [* -> *]) where
  lengthI :: Length fs
  lastIdxI ::
       Length fs -> Either (fs :~: '[]) (IIndex (Pred (Len fs)) fs (Last fs))
  replaceIdxI :: ReplaceW n fs g gs -> IIndex n gs g
  decompIdxI ::
       RemoveW n fs gs -> IIndex n fs f -> FSum fs a -> Either (FSum gs a) (f a)
  decompReplaceIdxI ::
       ReplaceW n fs g gs
    -> IIndex n fs f
    -> FSum fs a
    -> Either (FSum gs a) (f a)
  replaceTermI ::
       ReplaceW n fs g gs
    -> IIndex n fs f
    -> (f a -> g a)
    -> FSum fs a
    -> FSum gs a
  injectTerm :: IIndex n fs f -> f a -> FSum fs a
  inlI :: AppendW fs gs hs -> FSum fs a -> FSum hs a
  inrI :: AppendW fs gs hs -> FSum gs a -> FSum hs a
  fuseSumI ::
       (n == m) ~ 'False
    => RemoveW n fs fs'
    -> IIndex n fs f
    -> IIndex m fs f
    -> FSum fs a
    -> FSum fs' a
  injectReplaced :: ReplaceW i fs g fs' -> g a -> FSum fs' a
  fuseSumWithI ::
       (n == m) ~ 'False
    => (f a -> h a)
    -> (g a -> h a)
    -> RemoveW n fsrep res
    -> IIndex n fs f
    -> ReplaceW m fs h fsrep
    -> IIndex m fs g
    -> FSum fs a
    -> FSum res a
  fuseSumAllI :: (fs `AllEqual` f) => FSum fs a -> f a

instance Inductive '[] where
  lengthI = LZ
  {-# INLINE lengthI #-}
  lastIdxI _ = Left Refl
  {-# INLINE lastIdxI #-}
  replaceIdxI = absurdReplace
  {-# INLINE replaceIdxI #-}
  decompIdxI = absurdRemove
  {-# INLINE decompIdxI #-}
  decompReplaceIdxI = absurdReplace
  {-# INLINE decompReplaceIdxI #-}
  replaceTermI = absurdReplace
  {-# INLINE replaceTermI #-}
  injectTerm = absurdIdx
  {-# INLINE injectTerm #-}
  inlI _ = absurdFSum
  {-# INLINE inlI #-}
  inrI AppZ = id
  {-# INLINE inrI #-}
  fuseSumI _ _ _ = absurdFSum
  {-# INLINE fuseSumI #-}
  injectReplaced = absurdReplace
  {-# INLINE injectReplaced #-}
  fuseSumWithI _ _ _ _ _ _ = absurdFSum
  {-# INLINE fuseSumWithI #-}
  fuseSumAllI = absurdFSum
  {-# INLINE fuseSumAllI #-}

instance Inductive fs => Inductive (f : fs) where
  lengthI = LS lengthI
  {-# INLINE lengthI #-}
  lastIdxI (LS LZ) = Right IIZ
  lastIdxI (LS l@(LS _)) =
    case lastIdxI l of
      Right i -> Right (IIS i)
      Left r -> case r of {}
  {-# INLINE lastIdxI #-}
  replaceIdxI RepZ = IIZ
  replaceIdxI (RepS r) = IIS (replaceIdxI r)
  {-# INLINE replaceIdxI #-}
  decompIdxI RemZ IIZ (FInL x) = Right x
  decompIdxI RemZ IIZ (FInR x) = Left x
  decompIdxI (RemS _) (IIS _) (FInL x) = Left (FInL x)
  decompIdxI (RemS r) (IIS i) (FInR x) = first FInR (decompIdxI r i x)
  {-# INLINE decompIdxI #-}
  decompReplaceIdxI RepZ IIZ (FInL x) = Right x
  decompReplaceIdxI RepZ IIZ (FInR x) = Left (FInR x)
  decompReplaceIdxI (RepS _) (IIS _) (FInL x) = Left (FInL x)
  decompReplaceIdxI (RepS r) (IIS i) (FInR x) =
    first FInR (decompReplaceIdxI r i x)
  {-# INLINE decompReplaceIdxI #-}
  replaceTermI RepZ IIZ f (FInL x) = FInL (f x)
  replaceTermI RepZ IIZ _ (FInR x) = FInR x
  replaceTermI (RepS _) (IIS _) _ (FInL x) = FInL x
  replaceTermI (RepS r) (IIS i) f (FInR x) = FInR (replaceTermI r i f x)
  {-# INLINE replaceTermI #-}
  injectTerm IIZ = FInL
  injectTerm (IIS i) = FInR . injectTerm i
  {-# INLINE injectTerm #-}
  inlI (AppS _) (FInL x) = FInL x
  inlI (AppS a) (FInR x) = FInR (inlI a x)
  {-# INLINE inlI #-}
  inrI (AppS a) = FInR . inrI a
  {-# INLINE inrI #-}
  fuseSumI RemZ IIZ (IIS m) (FInL x) = injectTerm m x
  fuseSumI RemZ IIZ (IIS _) (FInR x) = x
  fuseSumI r@(RemS _) n@(IIS _) IIZ fsum =
    case decompIdxI r n fsum of
      Right x -> FInL x
      Left x -> x
  fuseSumI (RemS _) (IIS _) (IIS _) (FInL x) = FInL x
  fuseSumI (RemS r) (IIS n) (IIS m) (FInR x) = FInR (fuseSumI r n m x)
  {-# INLINE fuseSumI #-}
  injectReplaced RepZ = FInL
  injectReplaced (RepS r) = FInR . injectReplaced r
  {-# INLINE injectReplaced #-}
  fuseSumWithI f _ RemZ IIZ (RepS rep) (IIS _) (FInL x) =
    injectReplaced rep (f x)
  fuseSumWithI _ g RemZ IIZ (RepS rep) (IIS m) (FInR x) = replaceTermI rep m g x
  fuseSumWithI _ g (RemS _) (IIS _) RepZ IIZ (FInL x) = FInL (g x)
  fuseSumWithI f _ (RemS r) (IIS n) RepZ IIZ (FInR s) =
    case decompIdxI r n s of
      Right x -> FInL (f x)
      Left x -> FInR x
  fuseSumWithI _ _ (RemS _) (IIS _) (RepS _) (IIS _) (FInL x) = FInL x
  fuseSumWithI f g (RemS r) (IIS n) (RepS rep) (IIS m) (FInR x) =
    FInR (fuseSumWithI f g r n rep m x)
  {-# INLINE fuseSumWithI #-}
  fuseSumAllI (FInL x) = x
  fuseSumAllI (FInR x) = fuseSumAllI x
  {-# INLINE fuseSumAllI #-}

-- | Produce an index of a replaced element in the new list.
replaceIdx ::
     forall n a as b bs. (Inductive as, Replace n as b bs)
  => IIndex n as a
  -> IIndex n bs b
{-# INLINE replaceIdx #-}
replaceIdx _ = replaceIdxI (replaceW :: ReplaceW n as b bs)

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
     (Inductive fs, Remove n fs gs)
  => IIndex n fs f -- ^ An index of an element to be extracted
  -> FSum fs a
  -> Either (FSum gs a) (f a)
{-# INLINE fdecompIdx #-}
fdecompIdx = decompIdxI removeW

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
     forall n fs f p g gs a. (Inductive fs, Replace n fs g gs)
  => IIndex n fs f
  -> p g
  -> FSum fs a
  -> Either (FSum gs a) (f a)
{-# INLINE fdecompReplaceIdx #-}
fdecompReplaceIdx n _ = decompReplaceIdxI (replaceW :: ReplaceW n fs g gs) n

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
     forall n fs f g gs a. (Inductive fs, Replace n fs g gs)
  => IIndex n fs f -- ^ An index of a functor to be replaced.
  -> (f a -> g a) -- ^ A function used to transform old functor into a
     -- new one.
  -> FSum fs a -- ^ An old sum, which may or may not be represented by
               -- the functor in question.
  -> FSum gs a
{-# INLINE freplaceIdx #-}
freplaceIdx = replaceTermI replaceW

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
     forall n fs f a. Inductive fs
  => IIndex n fs f -- ^ An index at which to inject the functor.
  -> f a -- ^ The value to be injected.
  -> FSum fs a -- ^ A sum represented by the provided value at the
     -- provided index.
{-# INLINE finjectIdx #-}
finjectIdx = injectTerm

-- | Embed a sum into a sum of a larger list, obtained by adding
-- elements on the right.
--
-- This function does not, in a sense, change the /value/ stored, only
-- its /type/.
--
-- Since the 'Type.Family.List.++' type family is not injective, a
-- proxy argument is used to guide type inference.
finl ::
     forall fs gs hs proxy a. Append fs gs hs
  => proxy gs
  -> FSum fs a
  -> FSum hs a
{-# INLINE finl #-}
finl _ = inlI (appendW :: AppendW fs gs hs)

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
{-# INLINE finr #-}
finr _ = inrI (appendW :: AppendW fs gs hs)

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
fuseSum = fuseSumI removeW

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
fuseSumWith f g n' = fuseSumWithI f g removeW n' replaceW

-- | Unify /all/ of the terms in the sum, if they are all identical
-- (which is the meaning of a rather weird-looking constraint).
fuseSumAll :: (Inductive fs, fs `AllEqual` f) => FSum fs a -> f a
{-# INLINE fuseSumAll #-}
fuseSumAll = fuseSumAllI

-- | Require that all elements of list @bs@ are equal to @a@.
type family AllEqual bs a :: Constraint where
  '[] `AllEqual` a = ()
  (b : bs) `AllEqual` a = (a ~ b, bs `AllEqual` a)
