{-# LANGUAGE BangPatterns #-}
{-# LANGUAGE UndecidableInstances #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE StandaloneDeriving #-}
{-# LANGUAGE DeriveFunctor #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE FunctionalDependencies #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE KindSignatures #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE ScopedTypeVariables #-}

module Cobweb where

import Control.Monad (ap, forever, join, replicateM_)
import qualified Control.Monad.Fail as Fail
import Control.Monad.IO.Class (MonadIO(liftIO))
import Control.Monad.Morph (MFunctor(hoist))
import Control.Monad.Trans (MonadTrans(lift))
import Data.Bifunctor (first)
import Data.Foldable (traverse_)
import Data.Functor.Compose (Compose(getCompose))
import Data.Functor.Foldable (Base, Recursive(cata, project))
import Data.Proxy (Proxy(Proxy))
import Data.Void (absurd)

import Cobweb.Type.Combinators
import Data.Type.Length (Length)
import Data.Type.Sum.Lifted (FSum, nilFSum)
import Type.Class.Known (Known)
import Type.Class.Witness ((:-), Witness((\\)))
import Type.Family.List (type (++), Last, Null)
import Type.Family.Nat (Len, NatEq, Pred)

data NodeF (cs :: [* -> *]) (m :: * -> *) r a
  = ReturnF r
  | EffectF (m a)
  | ConnectF (FSum cs a)

deriving instance
         (All Functor cs, Functor m) => Functor (NodeF cs m r)

newtype Node cs m r = Node
  { getNode :: NodeF cs m r (Node cs m r)
  }

type instance Base (Node cs m r) = NodeF cs m r

instance (All Functor cs, Functor m) => Recursive (Node cs m r) where
  project = getNode

transform ::
     (All Functor cs, Functor m)
  => (NodeF cs m r (Node cs' m' r') -> NodeF cs' m' r' (Node cs' m' r'))
  -> Node cs m r
  -> Node cs' m' r'
transform alg = cata (Node . alg)

instance (All Functor cs, Functor m) => Functor (Node cs m) where
  fmap f = transform alg
    where
      alg (ReturnF r) = ReturnF (f r)
      alg (EffectF eff) = EffectF eff
      alg (ConnectF con) = ConnectF con

instance (All Functor cs, Functor m) => Applicative (Node cs m) where
  pure = Node . ReturnF
  (<*>) = ap

instance (All Functor cs, Functor m) => Monad (Node cs m) where
  x >>= f = transform alg x
    where
      alg (ReturnF r) = getNode (f r)
      alg (EffectF eff) = EffectF eff
      alg (ConnectF con) = ConnectF con

instance MonadTrans (Node cs) where
  lift eff = Node $ EffectF $ fmap (Node . ReturnF) eff

instance (All Functor cs, MonadIO m) => MonadIO (Node cs m) where
  liftIO = lift . liftIO

instance (All Functor cs, Fail.MonadFail m) => Fail.MonadFail (Node cs m) where
  fail = lift . Fail.fail

-- This instance is "undecidable", but it's fine, since HSum doesn't
-- actually know anything about Node, and expands in functor
-- instances for each interface in the list.
instance All Functor cs => MFunctor (Node cs) where
  hoist f = unsafeHoist f . observe

unsafeHoist ::
     (All Functor cs, Functor m)
  => (forall x. m x -> n x)
  -> Node cs m r
  -> Node cs n r
unsafeHoist f = transform alg
  where
    alg (ReturnF r) = ReturnF r
    alg (ConnectF con) = ConnectF con
    alg (EffectF eff) = EffectF (f eff)

inspect :: Monad m => Node cs m r -> m (Either r (FSum cs (Node cs m r)))
inspect (Node web) =
  case web of
    ReturnF r -> pure (Left r)
    EffectF eff -> eff >>= inspect
    ConnectF con -> pure (Right con)

unfold ::
     (Functor m, All Functor cs)
  => (b -> m (Either r (FSum cs b)))
  -> b
  -> Node cs m r
unfold step = loop
  where
    loop seed = Node (EffectF (fmap (Node . loopstep) (step seed)))
    loopstep (Left r) = ReturnF r
    loopstep (Right con) = ConnectF (fmap loop con)

observe :: (Monad m, All Functor cs) => Node cs m r -> Node cs m r
observe = unfold inspect

connects :: (All Functor cs) => FSum cs r -> Node cs m r
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

type Producer a = Node '[ Yielding a]

type Consumer a = Node '[ Awaiting a]

type Pipe a b = Node '[ Awaiting a, Yielding b]

type Effect = Node '[]

yieldOn :: IIndex n cs (Yielding a) -> a -> Node cs m ()
yieldOn n a = connectsOn n (a, ())

eachOn ::
     (Functor m, All Functor cs, Foldable f)
  => IIndex n cs (Yielding a)
  -> f a
  -> Node cs m ()
eachOn n = traverse_ (yieldOn n)

each :: (Foldable f, Functor m) => f a -> Producer a m ()
each = eachOn i0

awaitOn :: IIndex n cs (Awaiting a) -> Node cs m a
awaitOn n = connectsOn n id

onlyOne :: Node '[ c] m r -> Node '[ c] m r
onlyOne = id

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

mapping :: Functor m => (a -> b) -> Node '[ Awaiting a, Yielding b] m r
mapping f =
  forever $ do
    a <- awaitOn i0
    yieldOn i1 (f a)

premapOn ::
     (Functor m, All Functor cs, IReplaced n cs (Awaiting b) cs')
  => IIndex n cs (Awaiting a)
  -> (b -> a)
  -> Node cs m r
  -> Node cs' m r
premapOn n f = mapsOn n (. f)

foldOn ::
     (Functor m, IWithout n cs cs', All Functor cs')
  => (x -> a -> x)
  -> x
  -> (x -> b)
  -> IIndex n cs (Yielding a)
  -> Node cs m r
  -> Node cs' m (b, r)
foldOn comb seed fin n = loop seed
  where
    loop !z (Node web) =
      Node $
      case web of
        ReturnF r -> ReturnF (fin z, r)
        EffectF eff -> EffectF (fmap (loop z) eff)
        ConnectF con ->
          case fdecompIdx n con of
            Right (a, rest) -> getNode $ loop (comb z a) rest
            Left other -> ConnectF (fmap (loop z) other)

foldOnly ::
     Monad m => (x -> a -> x) -> x -> (x -> b) -> Producer a m r -> m (b, r)
foldOnly comb seed fin = run . foldOn comb seed fin i0

foldMOn ::
     (Functor m, IWithout n cs cs', All Functor cs')
  => (x -> a -> m x)
  -> m x
  -> (x -> m b)
  -> IIndex n cs (Yielding a)
  -> Node cs m r
  -> Node cs' m (b, r)
foldMOn comb seed fin n node' = Node (EffectF (fmap (flip loop node') seed))
  where
    loop !z (Node node) =
      Node $
      case node of
        ReturnF r -> EffectF (fmap (\b -> pure (b, r)) (fin z))
        EffectF eff -> EffectF (fmap (loop z) eff)
        ConnectF con ->
          case fdecompIdx n con of
            Left other -> ConnectF (fmap (loop z) other)
            Right (a, rest) -> EffectF (fmap (flip loop rest) (comb z a))

foldMOnly ::
     Monad m
  => (x -> a -> m x)
  -> m x
  -> (x -> m b)
  -> Producer a m r
  -> m (b, r)
foldMOnly comb seed fin = run . foldMOn comb seed fin i0

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

for ::
     (All Functor cs, Functor m)
  => (a -> Node cs m ())
  -> Producer a m r
  -> Node cs m r
for = forOn i0

zipping ::
     Functor m
  => (a -> b -> c)
  -> Node '[ Awaiting a, Awaiting b, Yielding c] m r
zipping f =
  forever $ do
    a <- awaitOn i0
    b <- awaitOn i1
    yieldOn i2 (f a b)

unzipping ::
     Functor m
  => (a -> (b, c))
  -> Node '[ Awaiting a, Yielding b, Yielding c] m r
unzipping f =
  forever $ do
    a <- awaitOn i0
    let (b, c) = f a
    yieldOn i1 b
    yieldOn i2 c

-- Fuse!
fuseCons ::
     (IWithout n cs cs', NatEq n k ~ 'False, Functor m, All Functor cs)
  => IIndex n cs c
  -> IIndex k cs c
  -> Node cs m r
  -> Node cs' m r
fuseCons n k = mapsAll (fuse n k)

-- Connecting
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

-- chunking
chunkBy ::
     (Functor c, Functor m)
  => Int
  -> Node '[ c] m r
  -> Node '[ Node '[ c] m] m r
chunkBy n = loop
  where
    loop node =
      Node $
      case getNode node of
        ReturnF r -> ReturnF r
        EffectF eff -> EffectF (fmap loop eff)
        ConnectF _ -> ConnectF (finjectIdx i0 $ chunkOff n node)
    chunkOff m node
      | m <= 0 = pure (loop node)
      | otherwise =
        Node $
        case getNode node of
          ReturnF r -> ReturnF (pure r)
          EffectF eff -> EffectF (fmap (chunkOff m) eff)
          ConnectF con -> ConnectF (fmap (chunkOff (m - 1)) con)

-- examples
connectTwo :: Monad m => Producer a m r -> Consumer a m r -> m r
connectTwo l r = run $ l |= r

stdoutLn :: MonadIO m => Consumer String m r
stdoutLn =
  forever $ do
    str <- awaitOn i0
    liftIO $ putStrLn str

stdinLn :: MonadIO m => Producer String m r
stdinLn = forever $ liftIO getLine >>= yieldOn i0

takeW :: Functor m => Int -> Node '[ Awaiting a, Yielding a] m ()
takeW n = replicateM_ n $ awaitOn i0 >>= yieldOn i1

tee :: Functor m => Node '[ Awaiting a, Yielding a, Yielding a] m r
tee =
  forever $ do
    a <- awaitOn i0
    yieldOn i1 a
    yieldOn i2 a

concatInputs ::
     (Functor m, Monoid a) => Node '[ Awaiting a, Awaiting a, Yielding a] m r
concatInputs = zipping mappend

-- FIXME figure out what it does and, depending on results,
-- a) rewrite it correctly;
-- b) rewrite it in a more understandable fashion, if it turns out to
-- be correct;
-- c) if none of the above applies/helps, at least explain what
-- happens here in comments.
distribute ::
     forall m t cs r.
     ( Monad m
     , MonadTrans t
     , MFunctor t
     , Monad (t m)
     , Monad (t (Node cs m))
     , All Functor cs
     )
  => Node cs (t m) r
  -> t (Node cs m) r
distribute = cata alg
  where
    alg :: NodeF cs (t m) r (t (Node cs m) r) -> t (Node cs m) r
    alg (ReturnF r) = pure r
    alg (EffectF eff) = join $ hoist lift eff
    alg (ConnectF con) = join $ lift $ connects con
