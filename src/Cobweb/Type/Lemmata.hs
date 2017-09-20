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
  ( appendConstraints
  , fmapAppend
  , fmapLength
  , appendAll
  , iwithoutRetainsLength
  , iwithoutRetainsAll
  , ireplacedRetainsAll
  ) where

import Cobweb.Type.Combinators
       (All, IIndex(IIS, IIZ), Remove, Replace)
import Data.Proxy (Proxy(Proxy))
import Data.Type.Length (Length(LS, LZ))
import Type.Class.Known (Known(known))
import Type.Class.Witness (Wit(Wit), Witness((\\)))
import Type.Family.List (type (++), type (<$>), ListC)

-- | If all constraints in both lists are satisfied, all constraints
-- in their concatenation are satisfied.
appendConstraints ::
     forall as bs p p'. (Known Length as, ListC as, ListC bs)
  => p as
  -> p' bs
  -> Wit (ListC (as ++ bs))
appendConstraints _ _ = loop (known :: Length as)
  where
    loop :: ListC as' => Length as' -> Wit (ListC (as' ++ bs))
    loop LZ = Wit
    loop (LS n) = Wit \\ loop n

-- | Map distributes over append.
fmapAppend ::
     forall f as bs p1 p2 p3. Known Length as
  => p1 f
  -> p2 as
  -> p3 bs
  -> Wit ((f <$> (as ++ bs)) ~ ((f <$> as) ++ (f <$> bs)))
fmapAppend _ _ _ = loop (known :: Length as)
  where
    loop ::
         Length as' -> Wit ((f <$> (as' ++ bs)) ~ ((f <$> as') ++ (f <$> bs)))
    loop LZ = Wit
    loop (LS n) = Wit \\ loop n

-- | Mapping preserves the knowledge of length (and the length itself,
-- but that is less important).
fmapLength ::
     forall as f p p2. Known Length as
  => p f
  -> p2 as
  -> Wit (Known Length (f <$> as))
fmapLength _ _ = loop (known :: Length as)
  where
    loop :: Length as' -> Wit (Known Length (f <$> as'))
    loop LZ = Wit
    loop (LS n) = Wit \\ loop n

-- | If all elements of @as@ and all elements of @bs@ satisfy some
-- constraint, then so do all elements in @as 'Type.Family.List.++' bs@.
appendAll ::
  forall p1 p2 p3 f as bs.
     (Known Length as, All f as, All f bs)
  => p1 f
  -> p2 as
  -> p3 bs
  -> Wit (All f (as ++ bs))
appendAll pf pa pb =
  Wit \\ fmapAppend pf pa pb \\ appendConstraints pfa pfb \\ fmapLength pf pa
  where
    pfa :: Proxy (f <$> as)
    pfa = Proxy
    pfb :: Proxy (f <$> bs)
    pfb = Proxy

-- | Removing an element from the list retains the knowledge of list's
-- length.
iwithoutRetainsLength ::
     Known Length as => IIndex n as a -> Wit (Known Length (Remove n as))
iwithoutRetainsLength IIZ = Wit
iwithoutRetainsLength (IIS n) = Wit \\ iwithoutRetainsLength n

-- | If all of the elements of the list satisfy some constraint, and
-- one element is removed, remaining elements still satisfy that
-- constraint.
iwithoutRetainsAll ::
     All f as => p f -> IIndex n as a -> Wit (All f (Remove n as))
iwithoutRetainsAll _ IIZ = Wit
iwithoutRetainsAll p (IIS n) = Wit \\ iwithoutRetainsAll p n

-- | If all of the elements of the list satisfy some constraint, and
-- one of them is replaced by another element that /also/ satisfies
-- that constraint, all elements of the resulting list satisfy that
-- constraint.
ireplacedRetainsAll ::
     (All f as, f b)
  => p b
  -> p' f
  -> IIndex n as a
  -> Wit (All f (Replace n as b))
ireplacedRetainsAll _ _ IIZ = Wit
ireplacedRetainsAll pb pf (IIS n) = Wit \\ ireplacedRetainsAll pb pf n
