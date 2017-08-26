{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE PolyKinds #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE EmptyCase #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE KindSignatures #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE ScopedTypeVariables #-}

module Data.Functor.HSum where

import Data.Type.Equality ((:~:)(Refl))
import Data.Proxy (Proxy(Proxy))
import Data.Bifunctor (bimap)

data HSum :: [* -> *] -> * -> * where
  This :: f a -> HSum (f : fs) a
  That :: HSum fs a -> HSum (f : fs) a

closed :: HSum '[] a -> b
closed x = case x of {}

instance Functor (HSum '[]) where
  fmap _ = closed

instance (Functor f, Functor (HSum fs)) => Functor (HSum (f : fs)) where
  fmap f (This x) = This (fmap f x)
  fmap f (That xs) = That (fmap f xs)

data Nat
  = Z
  | S Nat

type N0 = 'Z

type N1 = 'S N0

type N2 = 'S N1

type N3 = 'S N2

type N4 = 'S N3

type N5 = 'S N4

type N6 = 'S N5

type N7 = 'S N6

type N8 = 'S N7

type N9 = 'S N8

type family At (n :: Nat) (as :: [k]) :: k where
  At 'Z (a : as) = a
  At ('S n) (a : as) = At n as

type family Remove (n :: Nat) (as :: [k]) :: [k] where
  Remove 'Z (a : as) = as
  Remove ('S n) (a : as) = a : Remove n as

type family Insert (n :: Nat) (a :: k) (as :: [k]) :: [k] where
  Insert 'Z a as = a : as
  Insert ('S n) a (a' : as) = a' : Insert n a as

type family Replace (n :: Nat) (b :: k) (as :: [k]) :: [k] where
  Replace 'Z b (a : as) = b : as
  Replace ('S n) b (a : as) = a : Replace n b as

type family Concat (as :: [k]) (bs :: [k]) :: [k] where
  Concat '[] bs = bs
  Concat (a : as) bs = a : Concat as bs

data TNat :: Nat -> * where
  TZero :: TNat 'Z
  TSucc :: TNat n -> TNat ('S n)

t0 :: TNat N0
t0 = TZero

t1 :: TNat N1
t1 = TSucc t0

t2 :: TNat N2
t2 = TSucc t1

t3 :: TNat N3
t3 = TSucc t2

t4 :: TNat N4
t4 = TSucc t3

t5 :: TNat N5
t5 = TSucc t4

t6 :: TNat N6
t6 = TSucc t5

t7 :: TNat N7
t7 = TSucc t6

t8 :: TNat N8
t8 = TSucc t7

t9 :: TNat N9
t9 = TSucc t8

class Has (n :: Nat) (as :: [k]) where
  removeAndInsert :: TNat n -> as :~: Insert n (At n as) (Remove n as)

instance Has 'Z (a : as) where
  removeAndInsert TZero = Refl

instance Has n as => Has ('S n) (a : as) where
  removeAndInsert (TSucc n) =
    case (removeAndInsert n :: as :~: Insert n (At n as) (Remove n as)) of
      Refl -> Refl

extract :: TNat n -> HSum fs a -> Either (HSum (Remove n fs) a) (At n fs a)
extract TZero (This x) = Right x
extract TZero (That x) = Left x
extract (TSucc _) (This x) = Left (This x)
extract (TSucc n) (That x) = bimap That id (extract n x)

replace :: TNat n -> (At n fs a -> g a) -> HSum fs a -> HSum (Replace n g fs) a
replace TZero f (This x) = This (f x)
replace TZero _ (That x) = That x
replace (TSucc _) _ (This x) = This x
replace (TSucc n) f (That x) = That (replace n f x)

expand :: proxy f -> TNat n -> HSum fs a -> HSum (Insert n f fs) a
expand _ TZero x = That x
expand _ (TSucc _) (This x) = This x
expand p (TSucc n) (That x) = That (expand p n x)

inl :: proxy gs -> HSum fs a -> HSum (Concat fs gs) a
inl _ (This x) = This x
inl p (That x) = That (inl p x)

class Has n fs => HasHSum (n :: Nat) (fs :: [* -> *]) where
  embed :: (At n fs ~ f) => TNat n -> f a -> HSum fs a

instance HasHSum 'Z (f : fs) where
  embed TZero = This

instance HasHSum n fs => HasHSum ('S n) (f : fs) where
  embed (TSucc n) x = That (embed n x)

class FiniteHSum (fs :: [* -> *]) where
  inr :: proxy fs -> HSum gs a -> HSum (Concat fs gs) a

instance FiniteHSum '[] where
  inr _ = id

instance FiniteHSum fs => FiniteHSum (f : fs) where
  inr _ = That . inr (Proxy :: Proxy fs)

class Fusing n m cs where
  fuse :: TNat n -> TNat m -> HSum cs a -> HSum (Remove n cs) a

instance (At m cs ~ c, HasHSum m cs) => Fusing 'Z ('S m) (c : cs) where
  fuse TZero (TSucc m) hsum =
    case extract TZero hsum of
      Right c -> embed m c
      Left other -> other

instance (At n cs ~ c, HasHSum n cs) => Fusing ('S n) 'Z (c : cs) where
  fuse n TZero hsum =
    case extract n hsum of
      Right c -> This c
      Left other -> other

instance Fusing n m cs => Fusing ('S n) ('S m) (c : cs) where
  fuse (TSucc n) (TSucc m) hsum =
    case hsum of
      This x -> This x
      That other -> That (fuse n m other)
