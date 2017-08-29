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
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE PolyKinds #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeOperators #-}

module Cobweb.Type.Lemmata
  ( appendConstraints
  , fmapAppend
  , fmapLength
  , appendAll
  , iwithoutNonEmpty
  , iwithoutRetainsLength
  , iwithoutRetainsAll
  ) where

import Cobweb.Type.Combinators
       (All, IRemove(IRemS, IRemZ), IWithout, iwithout)
import Data.Kind (Constraint)
import Data.Proxy (Proxy(Proxy))
import Data.Type.Length (Length(LS, LZ))
import Type.Class.Known (Known(known))
import Type.Class.Witness ((:-)(Sub), Wit(Wit), Witness((\\)))
import Type.Family.List (type (++), type (<$>), ListC, Null)

-- | If all constraints in both lists are satisfied, all constraints
-- in their concatenation are satisfied.
appendConstraints ::
     forall as bs. (Known Length as, ListC as, ListC bs) :- ListC (as ++ bs)
appendConstraints = Sub $ loop (known :: Length as) (Proxy :: Proxy bs)
  where
    loop ::
         forall proxy as' bs'. (ListC as', ListC bs')
      => Length as'
      -> proxy bs'
      -> Wit (ListC (as' ++ bs'))
    loop LZ _ = Wit
    loop (LS n) p = Wit \\ loop n p

-- | Map distributes over append.
fmapAppend ::
     forall p1 p2 f as bs.
     p1 f
  -> p2 bs
  -> Known Length as :- ((f <$> (as ++ bs)) ~ ((f <$> as) ++ (f <$> bs)))
fmapAppend _ _ = Sub $ loop (known :: Length as)
  where
    loop ::
         forall as'.
         Length as'
      -> Wit ((f <$> (as' ++ bs)) ~ ((f <$> as') ++ (f <$> bs)))
    loop LZ = Wit
    loop (LS n) = Wit \\ loop n

-- | Mapping preserves the knowledge of length (and the length itself,
-- but that is less important).
fmapLength :: forall p f as. p f -> Known Length as :- Known Length (f <$> as)
fmapLength _ = Sub $ loop (known :: Length as)
  where
    loop :: forall as'. Length as' -> Wit (Known Length (f <$> as'))
    loop LZ = Wit
    loop (LS n) = Wit \\ loop n

-- | If all elements of @as@ and all elements of @bs@ satisfy some
-- constraint, then so do all elements in @as 'Type.Family.List.++' bs@.
appendAll ::
     forall p1 p2 (f :: k -> Constraint) (as :: [k]) (bs :: [k]).
     p1 f
  -> p2 bs
  -> (Known Length as, All f as, All f bs) :- All f (as ++ bs)
appendAll p1 p2 =
  Sub
    (Wit \\
     (fmapAppend p1 p2 :: Known Length as :- ((f <$> (as ++ bs)) ~ ((f <$> as) ++ (f <$> bs)))) \\
     (appendConstraints :: ( Known Length (f <$> as)
                           , ListC (f <$> as)
                           , ListC (f <$> bs)) :- ListC ((f <$> as) ++ (f <$> bs))) \\
     (fmapLength p1 :: Known Length as :- Known Length (f <$> as)))

-- | If it is possible to remove an element from the list, then the
-- list cannot be empty.
iwithoutNonEmpty :: forall n as bs. IWithout n as bs :- (Null as ~ 'False)
iwithoutNonEmpty =
  Sub $
  case (iwithout :: IRemove n as bs) of
    IRemZ -> Wit
    IRemS _ -> Wit

-- | Removing an element from the list retains the knowledge of list's
-- length.
iwithoutRetainsLength ::
     forall n as bs. (IWithout n as bs, Known Length as) :- Known Length bs
iwithoutRetainsLength =
  Sub $ loop (iwithout :: IRemove n as bs) (known :: Length as)
  where
    loop :: IRemove n' as' bs' -> Length as' -> Wit (Known Length bs')
    loop IRemZ l = Wit \\ l
    loop (IRemS r) (LS l) = Wit \\ loop r l

-- | If all of the elements of the list satisfy some constraint, and
-- one element is removed, remaining elements still satisfy that
-- constraint.
iwithoutRetainsAll ::
     forall p f n as bs. p f -> (IWithout n as bs, All f as) :- All f bs
iwithoutRetainsAll _ = Sub (loop (iwithout :: IRemove n as bs))
  where
    loop :: All f as' => IRemove n' as' bs' -> Wit (All f bs')
    loop IRemZ = Wit
    loop (IRemS r) = Wit \\ loop r
