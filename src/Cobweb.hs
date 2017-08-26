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
import Data.Functor.HSum
import Data.Proxy (Proxy(Proxy))

data NodeF (cs :: [* -> *]) (m :: * -> *) r a
  = ReturnF r
  | EffectF (m a)
  | ConnectF (HSum cs a)

deriving instance
         (Functor (HSum cs), Functor m) => Functor (NodeF cs m r)

newtype Node cs m r = Node
  { getNode :: NodeF cs m r (Node cs m r)
  }

type instance Base (Node cs m r) = NodeF cs m r

instance (Functor (HSum cs), Functor m) => Recursive (Node cs m r) where
  project = getNode

transform ::
     (Functor (HSum cs), Functor m)
  => (NodeF cs m r (Node cs' m' r') -> NodeF cs' m' r' (Node cs' m' r'))
  -> Node cs m r
  -> Node cs' m' r'
transform alg = cata (Node . alg)

instance (Functor (HSum cs), Functor m) => Functor (Node cs m) where
  fmap f = transform alg
    where
      alg (ReturnF r) = ReturnF (f r)
      alg (EffectF eff) = EffectF eff
      alg (ConnectF con) = ConnectF con

instance (Functor (HSum cs), Functor m) => Applicative (Node cs m) where
  pure = Node . ReturnF
  (<*>) = ap

instance (Functor (HSum cs), Functor m) => Monad (Node cs m) where
  x >>= f = transform alg x
    where
      alg (ReturnF r) = getNode (f r)
      alg (EffectF eff) = EffectF eff
      alg (ConnectF con) = ConnectF con

instance MonadTrans (Node cs) where
  lift eff = Node $ EffectF $ fmap (Node . ReturnF) eff

instance (Functor (HSum cs), MonadIO m) => MonadIO (Node cs m) where
  liftIO = lift . liftIO

instance (Functor (HSum cs), Fail.MonadFail m) =>
         Fail.MonadFail (Node cs m) where
  fail = lift . Fail.fail

-- This instance is "undecidable", but it's fine, since HSum doesn't
-- actually know anything about Node, and expands in functor
-- instances for each interface in the list.
instance Functor (HSum cs) => MFunctor (Node cs) where
  hoist f = unsafeHoist f . observe

unsafeHoist ::
     (Functor (HSum cs), Functor m)
  => (forall x. m x -> n x)
  -> Node cs m r
  -> Node cs n r
unsafeHoist f = transform alg
  where
    alg (ReturnF r) = ReturnF r
    alg (ConnectF con) = ConnectF con
    alg (EffectF eff) = EffectF (f eff)

inspect :: Monad m => Node cs m r -> m (Either r (HSum cs (Node cs m r)))
inspect (Node web) =
  case web of
    ReturnF r -> pure (Left r)
    EffectF eff -> eff >>= inspect
    ConnectF con -> pure (Right con)

unfold ::
     (Functor m, Functor (HSum cs))
  => (b -> m (Either r (HSum cs b)))
  -> b
  -> Node cs m r
unfold step = loop
  where
    loop seed = Node (EffectF (fmap (Node . loopstep) (step seed)))
    loopstep (Left r) = ReturnF r
    loopstep (Right con) = ConnectF (fmap loop con)

observe :: (Monad m, Functor (HSum cs)) => Node cs m r -> Node cs m r
observe = unfold inspect

connectsOn ::
     (HasHSum n cs, Functor c, At n cs ~ c) => TNat n -> c r -> Node cs m r
connectsOn n con = Node $ ConnectF $ embed n $ fmap (Node . ReturnF) con

run :: Monad m => Node '[] m r -> m r
run = cata alg
  where
    alg (ReturnF r) = pure r
    alg (EffectF eff) = join eff
    alg (ConnectF con) = closed con

type Yielding = (,)

type Awaiting = (->)

type Producer a m r = Node '[ Yielding a] m r

type Consumer a m r = Node '[ Awaiting a] m r

type Pipe a b m r = Node '[ Awaiting a, Yielding b] m r

yieldOn :: (HasHSum n cs, At n cs ~ Yielding a) => TNat n -> a -> Node cs m ()
yieldOn n a = connectsOn n (a, ())

eachOn ::
     ( HasHSum n cs
     , At n cs ~ Yielding a
     , Functor m
     , Functor (HSum cs)
     , Foldable f
     )
  => TNat n
  -> f a
  -> Node cs m ()
eachOn n = traverse_ (yieldOn n)

each :: (Foldable f, Functor m) => f a -> Producer a m ()
each = eachOn t0

awaitOn :: (HasHSum n cs, At n cs ~ Awaiting a) => TNat n -> Node cs m a
awaitOn n = connectsOn n id

onlyOne :: Node '[ c] m r -> Node '[ c] m r
onlyOne = id

mapsAll ::
     (Functor m, Functor (HSum cs))
  => (forall x. HSum cs x -> HSum cs' x)
  -> Node cs m r
  -> Node cs' m r
mapsAll f = transform alg
  where
    alg (ReturnF r) = ReturnF r
    alg (EffectF eff) = EffectF eff
    alg (ConnectF con) = ConnectF (f con)

mapsOn ::
     (Functor m, Functor (HSum cs))
  => TNat n
  -> (forall x. At n cs x -> c x)
  -> Node cs m r
  -> Node (Replace n c cs) m r
mapsOn n f = mapsAll (replace n f)

mapOn ::
     (Functor m, Functor (HSum cs), At n cs ~ Yielding a)
  => TNat n
  -> (a -> b)
  -> Node cs m r
  -> Node (Replace n (Yielding b) cs) m r
mapOn n f = mapsOn n (first f)

mapping :: Functor m => (a -> b) -> Node '[ Awaiting a, Yielding b] m r
mapping f =
  forever $ do
    a <- awaitOn t0
    yieldOn t1 (f a)

premapOn ::
     (Functor m, Functor (HSum cs), At n cs ~ Awaiting a)
  => TNat n
  -> (b -> a)
  -> Node cs m r
  -> Node (Replace n (Awaiting b) cs) m r
premapOn n f = mapsOn n (. f)

foldOn ::
     (Functor m, At n cs ~ Yielding a, Functor (HSum (Remove n cs)))
  => (x -> a -> x)
  -> x
  -> (x -> b)
  -> TNat n
  -> Node cs m r
  -> Node (Remove n cs) m (b, r)
foldOn comb seed fin n = loop seed
  where
    loop !z (Node web) =
      Node $
      case web of
        ReturnF r -> ReturnF (fin z, r)
        EffectF eff -> EffectF (fmap (loop z) eff)
        ConnectF con ->
          case extract n con of
            Right (a, rest) -> getNode $ loop (comb z a) rest
            Left other -> ConnectF (fmap (loop z) other)

foldOnly ::
     Monad m => (x -> a -> x) -> x -> (x -> b) -> Producer a m r -> m (b, r)
foldOnly comb seed fin = run . foldOn comb seed fin t0

foldMOn ::
     (Functor m, At n cs ~ Yielding a, Functor (HSum (Remove n cs)))
  => (x -> a -> m x)
  -> m x
  -> (x -> m b)
  -> TNat n
  -> Node cs m r
  -> Node (Remove n cs) m (b, r)
foldMOn comb seed fin n node' = Node (EffectF (fmap (flip loop node') seed))
  where
    loop !z (Node node) =
      Node $
      case node of
        ReturnF r -> EffectF (fmap (\b -> pure (b, r)) (fin z))
        EffectF eff -> EffectF (fmap (loop z) eff)
        ConnectF con ->
          case extract n con of
            Left other -> ConnectF (fmap (loop z) other)
            Right (a, rest) -> EffectF (fmap (flip loop rest) (comb z a))

foldMOnly ::
     Monad m
  => (x -> a -> m x)
  -> m x
  -> (x -> m b)
  -> Producer a m r
  -> m (b, r)
foldMOnly comb seed fin = run . foldMOn comb seed fin t0

forsOn ::
     forall m n cs cs' r.
     ( Functor m
     , Functor (HSum cs)
     , Functor (HSum (Concat (Remove n cs) cs'))
     , Functor (HSum cs')
     , FiniteHSum (Remove n cs)
     )
  => TNat n
  -> (forall x. At n cs x -> Node cs' m x)
  -> Node cs m r
  -> Node (Concat (Remove n cs) cs') m r
forsOn n f = transform alg
  where
    alg (ReturnF r) = ReturnF r
    alg (EffectF eff) = EffectF eff
    alg (ConnectF con) =
      case extract n con of
        Left other -> ConnectF (inl proxyInner other)
        Right c -> getNode $ join $ mapsAll (inr proxyOuter) $ f c
    proxyInner :: Proxy cs'
    proxyInner = Proxy
    proxyOuter :: Proxy (Remove n cs)
    proxyOuter = Proxy

forOn ::
     ( Functor m
     , Functor (HSum cs)
     , Functor (HSum (Concat (Remove n cs) cs'))
     , Functor (HSum cs')
     , FiniteHSum (Remove n cs)
     , At n cs ~ Yielding a
     )
  => TNat n
  -> (a -> Node cs' m ())
  -> Node cs m r
  -> Node (Concat (Remove n cs) cs') m r
forOn n f = forsOn n (\(a, r) -> r <$ f a)

for ::
     (Functor (HSum cs), Functor m)
  => (a -> Node cs m ())
  -> Producer a m r
  -> Node cs m r
for = forOn t0

zipping ::
     Functor m
  => (a -> b -> c)
  -> Node '[ Awaiting a, Awaiting b, Yielding c] m r
zipping f =
  forever $ do
    a <- awaitOn t0
    b <- awaitOn t1
    yieldOn t2 (f a b)

unzipping ::
     Functor m
  => (a -> (b, c))
  -> Node '[ Awaiting a, Yielding b, Yielding c] m r
unzipping f =
  forever $ do
    a <- awaitOn t0
    let (b, c) = f a
    yieldOn t1 b
    yieldOn t2 c

-- Fuse!

fuseCons ::
     (Fusing n k cs, Functor m, Functor (HSum cs))
  => TNat n
  -> TNat k
  -> Node cs m r
  -> Node (Remove n cs) m r
fuseCons n k = mapsAll (fuse n k)

-- Connecting
class Annihilate f g | f -> g, g -> f where
  annihilate :: f a -> g b -> (a, b)

instance Annihilate ((,) e) ((->) e) where
  annihilate (e, a) fb = (a, fb e)

instance Annihilate ((->) e) ((,) e) where
  annihilate fa (e, b) = (fa e, b)

connectOn ::
     forall n k lcs rcs m r.
     ( FiniteHSum (Remove n lcs)
     , Functor (HSum (Remove n lcs))
     , Functor (HSum (Remove k rcs))
     , Annihilate (At n lcs) (At k rcs)
     , Functor m
     )
  => TNat n
  -> TNat k
  -> Node lcs m r
  -> Node rcs m r
  -> Node (Concat (Remove n lcs) (Remove k rcs)) m r
connectOn n k left right =
  Node $
  case getNode right of
    ReturnF r -> ReturnF r
    EffectF eff -> EffectF (fmap (connectOn n k left) eff)
    ConnectF hsum ->
      case extract k hsum of
        Left other -> ConnectF (inr proxyL (fmap (connectOn n k left) other))
        Right con -> getNode $ provideUpstream left con
  where
    provideUpstream ::
         Node lcs m r
      -> At k rcs (Node rcs m r)
      -> Node (Concat (Remove n lcs) (Remove k rcs)) m r
    provideUpstream l r =
      Node $
      case getNode l of
        ReturnF x -> ReturnF x
        EffectF eff -> EffectF (fmap (`provideUpstream` r) eff)
        ConnectF hsum ->
          case extract n hsum of
            Left other ->
              ConnectF (inl proxyR (fmap (`provideUpstream` r) other))
            Right lcon ->
              let (l', r') = annihilate lcon r
              in getNode $ connectOn n k l' r'
    proxyR = Proxy :: Proxy (Remove k rcs)
    proxyL = Proxy :: Proxy (Remove n lcs)

pullOn ::
     forall n k lcs rcs lreq lresp rreq rresp m r.
     ( FiniteHSum (Remove n lcs)
     , Functor (HSum (Remove n lcs))
     , Functor (HSum (Remove k rcs))
     , At n lcs ~ Compose lresp lreq
     , At k rcs ~ Compose rresp rreq
     , Annihilate lresp rreq
     , Annihilate rresp lreq
     , Functor m
     )
  => TNat n
  -> TNat k
  -> lreq (Node lcs m r)
  -> Node rcs m r
  -> Node (Concat (Remove n lcs) (Remove k rcs)) m r
pullOn n k left right =
  Node $
  case getNode right of
    ReturnF r -> ReturnF r
    EffectF eff -> EffectF (fmap (pullOn n k left) eff)
    ConnectF hsum ->
      case extract k hsum of
        Left other -> ConnectF (inr proxyL (fmap (pullOn n k left) other))
        Right con ->
          let (r', l') = annihilate (getCompose con) left
          in getNode $ pushOn n k l' r'
  where
    proxyL :: Proxy (Remove n lcs)
    proxyL = Proxy

pushOn ::
     forall n k lcs rcs lreq lresp rreq rresp m r.
     ( FiniteHSum (Remove n lcs)
     , Functor (HSum (Remove n lcs))
     , Functor (HSum (Remove k rcs))
     , At n lcs ~ Compose lresp lreq
     , At k rcs ~ Compose rresp rreq
     , Annihilate lresp rreq
     , Annihilate rresp lreq
     , Functor m
     )
  => TNat n
  -> TNat k
  -> Node lcs m r
  -> rreq (Node rcs m r)
  -> Node (Concat (Remove n lcs) (Remove k rcs)) m r
pushOn n k left right =
  Node $
  case getNode left of
    ReturnF r -> ReturnF r
    EffectF eff -> EffectF (fmap (\l -> pushOn n k l right) eff)
    ConnectF hsum ->
      case extract n hsum of
        Left other ->
          ConnectF (inl proxyR (fmap (\l -> pushOn n k l right) other))
        Right con ->
          let (l', r') = annihilate (getCompose con) right
          in getNode $ pullOn n k l' r'
  where
    proxyR :: Proxy (Remove k rcs)
    proxyR = Proxy

connectOn0 ::
     ( Functor (HSum lcs)
     , FiniteHSum lcs
     , Functor (HSum rcs)
     , Functor m
     , Annihilate l r
     )
  => Node (l : lcs) m a
  -> Node (r : rcs) m a
  -> Node (Concat lcs rcs) m a
connectOn0 = connectOn t0 t0

(|=) ::
     ( Functor (HSum lcs)
     , FiniteHSum lcs
     , Functor (HSum rcs)
     , Functor m
     , Annihilate l r
     )
  => Node (l : lcs) m a
  -> Node (r : rcs) m a
  -> Node (Concat lcs rcs) m a
(|=) = connectOn0

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
        ConnectF _ -> ConnectF (embed t0 $ chunkOff n node)
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

connectPipe ::
     (Functor i, Functor o, Annihilate o' i', Functor m)
  => Node '[ i, o'] m r
  -> Node '[ i', o] m r
  -> Node '[ i, o] m r
connectPipe = connectOn t1 t0

stdoutLn :: MonadIO m => Consumer String m r
stdoutLn =
  forever $ do
    str <- awaitOn t0
    liftIO $ putStrLn str

stdinLn :: MonadIO m => Producer String m r
stdinLn = forever $ liftIO getLine >>= yieldOn t0

takeW :: Functor m => Int -> Node '[ Awaiting a, Yielding a] m ()
takeW n = replicateM_ n $ awaitOn t0 >>= yieldOn t1

tee :: Functor m => Node '[ Awaiting a, Yielding a, Yielding a] m r
tee =
  forever $ do
    a <- awaitOn t0
    yieldOn t1 a
    yieldOn t2 a

concatInputs ::
     (Functor m, Monoid a) => Node '[ Awaiting a, Awaiting a, Yielding a] m r
concatInputs = zipping mappend
