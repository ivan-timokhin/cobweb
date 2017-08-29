{-# LANGUAGE DataKinds #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE FunctionalDependencies #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE TypeOperators #-}

module Cobweb.Link where

import Data.Functor.Compose (Compose(getCompose))
import Data.Proxy (Proxy(Proxy))
import Data.Type.Length (Length)
import Type.Class.Known (Known)
import Type.Class.Witness ((:-), Witness((\\)))
import Type.Family.List (type (++), Last, Null)
import Type.Family.Nat (Len, Pred)

import Cobweb.Internal
       (Node(Node, getNode), NodeF(ConnectF, EffectF, ReturnF))
import Cobweb.Type.Combinators
       (All, IIndex, IWithout, fdecompIdx, finl, finr, i0, lastIndex)
import Cobweb.Type.Lemmata
       (iwithoutNonEmpty, iwithoutRetainsLength)

class Annihilate f g | f -> g, g -> f where
  annihilate :: f a -> g b -> (a, b)

instance Annihilate ((,) e) ((->) e) where
  annihilate (e, a) fb = (a, fb e)

instance Annihilate ((->) e) ((,) e) where
  annihilate fa (e, b) = (fa e, b)

(|$) ::
     forall lcs lcs' r rcs' m a.
     ( IWithout (Pred (Len lcs)) lcs lcs'
     , Known Length lcs
     , All Functor lcs'
     , All Functor rcs'
     , Annihilate (Last lcs) r
     , Functor m
     )
  => Node lcs m a
  -> Node (r : rcs') m a
  -> Node (lcs' ++ rcs') m a
(|$) =
  connectPipe_ \\
  (iwithoutNonEmpty :: IWithout (Pred (Len lcs)) lcs lcs' :- (Null lcs ~ 'False)) \\
  (iwithoutRetainsLength :: ( IWithout (Pred (Len lcs)) lcs lcs'
                            , Known Length lcs) :- Known Length lcs')

connectPipe_ ::
     ( IWithout (Pred (Len lcs)) lcs lcs'
     , Known Length lcs
     , Known Length lcs'
     , Null lcs ~ 'False
     , All Functor lcs'
     , All Functor rcs'
     , Annihilate (Last lcs) r
     , Functor m
     )
  => Node lcs m a
  -> Node (r : rcs') m a
  -> Node (lcs' ++ rcs') m a
connectPipe_ = connectOn lastIndex i0

connectOn ::
     forall n k lcs lcs' lc rcs rcs' rc m r.
     ( IWithout n lcs lcs'
     , IWithout k rcs rcs'
     , Known Length lcs'
     , All Functor lcs'
     , All Functor rcs'
     , Annihilate lc rc
     , Functor m
     )
  => IIndex n lcs lc
  -> IIndex k rcs rc
  -> Node lcs m r
  -> Node rcs m r
  -> Node (lcs' ++ rcs') m r
connectOn n k left right =
  Node $
  case getNode right of
    ReturnF r -> ReturnF r
    EffectF eff -> EffectF (fmap (connectOn n k left) eff)
    ConnectF hsum ->
      case fdecompIdx k hsum of
        Left other -> ConnectF (finr proxyL (fmap (connectOn n k left) other))
        Right con -> getNode $ provideUpstream left con
  where
    provideUpstream ::
         Node lcs m r -> rc (Node rcs m r) -> Node (lcs' ++ rcs') m r
    provideUpstream l r =
      Node $
      case getNode l of
        ReturnF x -> ReturnF x
        EffectF eff -> EffectF (fmap (`provideUpstream` r) eff)
        ConnectF hsum ->
          case fdecompIdx n hsum of
            Left other ->
              ConnectF (finl proxyR (fmap (`provideUpstream` r) other))
            Right lcon ->
              let (l', r') = annihilate lcon r
              in getNode $ connectOn n k l' r'
    proxyR = Proxy :: Proxy rcs'
    proxyL = Proxy :: Proxy lcs'

pullOn ::
     forall n k lcs lcs' rcs rcs' lreq lresp rreq rresp m r.
     ( IWithout n lcs lcs'
     , IWithout k rcs rcs'
     , Known Length lcs'
     , All Functor lcs'
     , All Functor rcs'
     , Annihilate lresp rreq
     , Annihilate rresp lreq
     , Functor m
     )
  => IIndex n lcs (Compose lresp lreq)
  -> IIndex k rcs (Compose rresp rreq)
  -> lreq (Node lcs m r)
  -> Node rcs m r
  -> Node (lcs' ++ rcs') m r
pullOn n k left right =
  Node $
  case getNode right of
    ReturnF r -> ReturnF r
    EffectF eff -> EffectF (fmap (pullOn n k left) eff)
    ConnectF hsum ->
      case fdecompIdx k hsum of
        Left other -> ConnectF (finr proxyL (fmap (pullOn n k left) other))
        Right con ->
          let (r', l') = annihilate (getCompose con) left
          in getNode $ pushOn n k l' r'
  where
    proxyL :: Proxy lcs'
    proxyL = Proxy

pushOn ::
     forall n k lcs lcs' rcs rcs' lreq lresp rreq rresp m r.
     ( IWithout n lcs lcs'
     , IWithout k rcs rcs'
     , Known Length lcs'
     , All Functor lcs'
     , All Functor rcs'
     , Annihilate lresp rreq
     , Annihilate rresp lreq
     , Functor m
     )
  => IIndex n lcs (Compose lresp lreq)
  -> IIndex k rcs (Compose rresp rreq)
  -> Node lcs m r
  -> rreq (Node rcs m r)
  -> Node (lcs' ++ rcs') m r
pushOn n k left right =
  Node $
  case getNode left of
    ReturnF r -> ReturnF r
    EffectF eff -> EffectF (fmap (\l -> pushOn n k l right) eff)
    ConnectF hsum ->
      case fdecompIdx n hsum of
        Left other ->
          ConnectF (finl proxyR (fmap (\l -> pushOn n k l right) other))
        Right con ->
          let (l', r') = annihilate (getCompose con) right
          in getNode $ pullOn n k l' r'
  where
    proxyR :: Proxy rcs'
    proxyR = Proxy

(|=) ::
     ( All Functor lcs
     , Known Length lcs
     , All Functor rcs
     , Annihilate l r
     , Functor m
     )
  => Node (l : lcs) m a
  -> Node (r : rcs) m a
  -> Node (lcs ++ rcs) m a
(|=) = connectOn i0 i0

infixl 5 |=
