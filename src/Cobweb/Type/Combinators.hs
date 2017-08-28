{-# LANGUAGE ConstraintKinds #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE UndecidableInstances #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE FunctionalDependencies #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE PolyKinds #-}
{-# LANGUAGE ScopedTypeVariables #-}

module Cobweb.Type.Combinators where

import Data.Bifunctor (bimap)
import Data.Kind (Constraint)
import Data.Proxy (Proxy(Proxy))
import Data.Type.Index (Index(IS, IZ))
import Data.Type.Length (Length(LS, LZ))
import Data.Type.Sum.Lifted (FSum(FInL, FInR), injectFSum)
import Type.Class.Known (Known(known))
import Type.Class.Witness ((:-)(Sub), Wit(Wit), Witness((\\)))
import Type.Family.Constraint (ØC)
import Type.Family.List (type (++), type (<$>), Last, ListC, Null)
import Type.Family.Nat
       (Len, N(S, Z), N0, N1, N10, N2, N3, N4, N5, N6, N7, N8, N9, NatEq,
        Pred)

type All f as = ListC (f <$> as)

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

fmapLength :: forall p f as. p f -> Known Length as :- Known Length (f <$> as)
fmapLength _ = Sub $ loop (known :: Length as)
  where
    loop :: forall as'. Length as' -> Wit (Known Length (f <$> as'))
    loop LZ = Wit
    loop (LS n) = Wit \\ loop n

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

data IIndex :: N -> [k] -> k -> * where
  IIZ :: IIndex 'Z (a : as) a
  IIS :: !(IIndex n as a) -> IIndex ('S n) (b : as) a

forgetIdx :: IIndex n as a -> Index as a
forgetIdx IIZ = IZ
forgetIdx (IIS n) = IS (forgetIdx n)

data IRemove :: N -> [k] -> [k] -> * where
  IRemZ :: IRemove 'Z (a : as) as
  IRemS :: !(IRemove n as bs) -> IRemove ('S n) (a : as) (a : bs)

class IWithout (n :: N) (as :: [k]) (bs :: [k]) | n as -> bs where
  iwithout :: IRemove n as bs

instance IWithout 'Z (a : as) as where
  iwithout = IRemZ

instance IWithout n as bs => IWithout ('S n) (a : as) (a : bs) where
  iwithout = IRemS iwithout

instance Witness ØC (IWithout n as bs) (IRemove n as bs) where
  f \\ IRemZ = f
  f \\ IRemS r = f \\ r

iwithoutNonEmpty :: forall n as bs. IWithout n as bs :- (Null as ~ 'False)
iwithoutNonEmpty =
  Sub $
  case (iwithout :: IRemove n as bs) of
    IRemZ -> Wit
    IRemS _ -> Wit

iwithoutRetainsLength ::
     forall n as bs. (IWithout n as bs, Known Length as) :- Known Length bs
iwithoutRetainsLength =
  Sub $ loop (iwithout :: IRemove n as bs) (known :: Length as)
  where
    loop :: IRemove n' as' bs' -> Length as' -> Wit (Known Length bs')
    loop IRemZ l = Wit \\ l
    loop (IRemS r) (LS l) = Wit \\ loop r l

iwithoutRetainsAll ::
     forall p f n as bs. p f -> (IWithout n as bs, All f as) :- All f bs
iwithoutRetainsAll _ = Sub (loop (iwithout :: IRemove n as bs))
  where
    loop :: All f as' => IRemove n' as' bs' -> Wit (All f bs')
    loop IRemZ = Wit
    loop (IRemS r) = Wit \\ loop r

fdecompIdx ::
     IWithout n fs gs => IIndex n fs f -> FSum fs a -> Either (FSum gs a) (f a)
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
    loop (IRemS r) (IIS n) (FInR fs) = bimap FInR id (loop r n fs)

data IReplace :: N -> [k] -> k -> [k] -> * where
  IRepZ :: IReplace 'Z (a : as) b (b : as)
  IRepS :: !(IReplace n as b bs) -> IReplace ('S n) (a : as) b (a : bs)

class IReplaced n as b bs | n as b -> bs where
  ireplace :: IReplace n as b bs

instance IReplaced 'Z (a : as) b (b : as) where
  ireplace = IRepZ

instance IReplaced n as b bs => IReplaced ('S n) (a : as) b (a : bs) where
  ireplace = IRepS ireplace

instance Witness ØC (IReplaced n as b bs) (IReplace n as b bs) where
  f \\ IRepZ = f
  f \\ IRepS r = f \\ r

freplaceIdx ::
     IReplaced n fs g gs
  => IIndex n fs f
  -> (f a -> g a)
  -> FSum fs a
  -> FSum gs a
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

finjectIdx :: IIndex n fs f -> f a -> FSum fs a
finjectIdx = injectFSum . forgetIdx

finl :: proxy gs -> FSum fs a -> FSum (fs ++ gs) a
finl _ (FInL f) = FInL f
finl proxy (FInR f) = FInR (finl proxy f)

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
