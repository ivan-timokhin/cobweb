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
