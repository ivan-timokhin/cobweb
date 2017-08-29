{-# LANGUAGE DataKinds #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeOperators #-}

module Cobweb.Core where

import Control.Monad (join)
import Data.Bifunctor (first)
import Data.Foldable (traverse_)
import Data.Functor.Foldable (Recursive(cata))
import Data.Proxy (Proxy(Proxy))
import Data.Type.Length (Length)
import Data.Type.Sum.Lifted (FSum, nilFSum)
import Data.Void (absurd)
import Type.Class.Known (Known)
import Type.Class.Witness ((:-), Witness((\\)))
import Type.Family.List (type (++))

import Cobweb.Internal
       (Node(Node, getNode), NodeF(ConnectF, EffectF, ReturnF), transform)
import Cobweb.Type.Combinators
       (All, IIndex, IReplaced, IWithout, fdecompIdx, finjectIdx, finl,
        finr, freplaceIdx)
import Cobweb.Type.Lemmata (appendAll, iwithoutRetainsAll)

connects :: All Functor cs => FSum cs r -> Node cs m r
connects con = Node $ ConnectF $ fmap (Node . ReturnF) con

connectsOn :: Functor c => IIndex n cs c -> c r -> Node cs m r
connectsOn n con = Node $ ConnectF $ finjectIdx n $ fmap (Node . ReturnF) con

run :: Monad m => Effect m r -> m r
run = cata alg
  where
    alg (ReturnF r) = pure r
    alg (EffectF eff) = join eff
    alg (ConnectF con) = absurd (nilFSum con)

type Yielding = (,)

type Awaiting = (->)

type Effect = Node '[]

yieldOn :: IIndex n cs (Yielding a) -> a -> Node cs m ()
yieldOn n a = connectsOn n (a, ())

eachOn ::
     (Functor m, All Functor cs, Foldable f)
  => IIndex n cs (Yielding a)
  -> f a
  -> Node cs m ()
eachOn n = traverse_ (yieldOn n)

awaitOn :: IIndex n cs (Awaiting a) -> Node cs m a
awaitOn n = connectsOn n id

mapsAll ::
     (Functor m, All Functor cs)
  => (forall x. FSum cs x -> FSum cs' x)
  -> Node cs m r
  -> Node cs' m r
mapsAll f = transform alg
  where
    alg (ReturnF r) = ReturnF r
    alg (EffectF eff) = EffectF eff
    alg (ConnectF con) = ConnectF (f con)

mapsOn ::
     (Functor m, All Functor cs, IReplaced n cs c' cs')
  => IIndex n cs c
  -> (forall x. c x -> c' x)
  -> Node cs m r
  -> Node cs' m r
mapsOn n f = mapsAll (freplaceIdx n f)

mapOn ::
     (Functor m, All Functor cs, IReplaced n cs (Yielding b) cs')
  => IIndex n cs (Yielding a)
  -> (a -> b)
  -> Node cs m r
  -> Node cs' m r
mapOn n f = mapsOn n (first f)

premapOn ::
     (Functor m, All Functor cs, IReplaced n cs (Awaiting b) cs')
  => IIndex n cs (Awaiting a)
  -> (b -> a)
  -> Node cs m r
  -> Node cs' m r
premapOn n f = mapsOn n (. f)

forsOn ::
     forall m n cs cs' cs'' r c.
     ( Functor m
     , All Functor cs
     , IWithout n cs cs''
     , Known Length cs''
     , All Functor cs'
     )
  => IIndex n cs c
  -> (forall x. c x -> Node cs' m x)
  -> Node cs m r
  -> Node (cs'' ++ cs') m r
forsOn idx f =
  forsOn_ idx f \\
  (appendAll (Proxy :: Proxy Functor) (Proxy :: Proxy cs') :: ( Known Length cs''
                                                              , All Functor cs''
                                                              , All Functor cs') :- All Functor (cs'' ++ cs')) \\
  (iwithoutRetainsAll (Proxy :: Proxy Functor) :: ( IWithout n cs cs''
                                                  , All Functor cs) :- All Functor cs'')

forsOn_ ::
     forall m n cs cs' cs'' r c.
     ( Functor m
     , All Functor cs
     , IWithout n cs cs''
     , All Functor (cs'' ++ cs')
     , All Functor cs'
     , Known Length cs''
     )
  => IIndex n cs c
  -> (forall x. c x -> Node cs' m x)
  -> Node cs m r
  -> Node (cs'' ++ cs') m r
forsOn_ n f = transform alg
  where
    alg (ReturnF r) = ReturnF r
    alg (EffectF eff) = EffectF eff
    alg (ConnectF con) =
      case fdecompIdx n con of
        Left other -> ConnectF (finl proxyInner other)
        Right c -> getNode $ join $ mapsAll (finr proxyOuter) $ f c
    proxyInner :: Proxy cs'
    proxyInner = Proxy
    proxyOuter :: Proxy cs''
    proxyOuter = Proxy

forOn ::
     ( Functor m
     , All Functor cs
     , IWithout n cs cs''
     , All Functor cs'
     , Known Length cs''
     )
  => IIndex n cs (Yielding a)
  -> (a -> Node cs' m ())
  -> Node cs m r
  -> Node (cs'' ++ cs') m r
forOn n f = forsOn n (\(a, r) -> r <$ f a)
