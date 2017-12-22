{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE ScopedTypeVariables #-}

module Cobweb.Internal.Cat
  ( Cat(Leaf, Cat)
  , unconsCat
  , (|>)
  ) where

data Cat k a b where
  Leaf :: k a b -> Cat k a b
  Cat :: Cat k a x -> Cat k x b -> Cat k a b

unconsCat ::
     forall k a b r.
     (k a b -> r)
  -> (forall x. k a x -> Cat k x b -> r)
  -> Cat k a b
  -> r
{-# INLINE unconsCat #-}
unconsCat f _ (Leaf k) = f k
unconsCat _ g (Cat l r) = go l r
  where
    go :: Cat k a y -> Cat k y b -> r
    go (Leaf x) = g x
    go (Cat l' r') = go l' . Cat r'

(|>) :: Cat k a b -> k b c -> Cat k a c
{-# INLINE (|>) #-}
(|>) c = Cat c . Leaf

infixl 5 |>
