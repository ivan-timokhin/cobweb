{-|
Module: Cobweb.Internal
Description: Exposes internal workings of Node
Copyright: 2017 © Ivan Timokhin
License: BSD3
Maintainer: timokhin.iv@gmail.com
Stability: experimental

Underneath, 'Node' is a free monad over sum of @m@ and all of
communication functors.

This has important implication in that 'Node' violates monad
transformer laws.  Both of them, actually:

  [@'lift' . 'return' = 'return'@] is violated because the former has
  an 'EffectF' layer on top, while the latter is purely 'ReturnF';

  [@'lift' (m '>>=' f) = 'lift' m '>>=' ('lift' . f)@] is violated
  because the former will have one 'EffectF' layer, while the latter
  two.

Neither of these should be visible without importing this module so
any visible violation of monad transformer laws is still a bug in the
library.  However, this structural violation means that data types and
functions defined in this module should be handled with care, as they
are potentially unsafe.

The motivation for said design primarily stems from the desire to
avoid ‘dropping’ into the base monad at every step, even when we're
simply trying to pass around some values through communication
channels, with no effects from the base monad required.
-}
{-# OPTIONS_HADDOCK show-extensions #-}
{-# LANGUAGE BangPatterns #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE UndecidableInstances #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE LambdaCase #-}

module Cobweb.Internal
  ( Node
  , cata
  , build
  , unconsNode
  , unsafeHoist
  , inspect
  , unfold
  , observe
  ) where

import Control.Arrow (Kleisli(Kleisli, runKleisli))
import Control.Monad (ap, liftM)
import Control.Monad.Base (MonadBase(liftBase))
import Control.Monad.Catch (MonadCatch(catch), MonadThrow(throwM))
import Control.Monad.Except (MonadError(catchError, throwError))
import qualified Control.Monad.Fail as Fail
import Control.Monad.IO.Class (MonadIO(liftIO))
import Control.Monad.Morph (MFunctor(hoist), MMonad(embed))
import Control.Monad.Primitive (PrimMonad(PrimState, primitive))
import Control.Monad.RWS.Class (MonadRWS)
import Control.Monad.Reader.Class (MonadReader(ask, local, reader))
import Control.Monad.State.Class (MonadState(get, put, state))
import Control.Monad.Trans (MonadTrans(lift))
import Control.Monad.Trans.Resource (MonadResource(liftResourceT))
import Control.Monad.Writer.Class
  ( MonadWriter(listen, pass, tell, writer)
  , censor
  )
import Data.Functor.Coyoneda (liftCoyoneda, lowerCoyoneda, Coyoneda(Coyoneda))
import Data.Functor.Sum (Sum(InL, InR))

import Cobweb.Type.Combinators (FSum)
import Cobweb.Internal.Cat (Cat(Cat, Leaf), (|>), unconsCat)

-- | A monad transformer that extends the underlying monad @m@ with a
-- capacity to communicate on a list of channels @cs@.
--
-- Channels are 'Functor's, values of which can be embedded into the
-- computation.  For example,
--
-- @
-- 'Node' '[(,) a, (->) b, (,) c] m r
-- @
--
-- produces values of type @a@ on the first channel, consumes values
-- of type @b@ on the second, and produces values of type @c@ on the
-- third.  "Cobweb.Core" provides aliases for these (most common)
-- channel types: 'Cobweb.Core.Yield' for @(,)@, and
-- 'Cobweb.Core.Await' for @(->)@.
data Node cs m a where
  Pure :: a -> Node cs m a
  Impure :: Sum m (FSum cs) x -> Cat (Kleisli (Node cs m)) x a -> Node cs m a

unconsNode ::
  forall a r cs m.
     (a -> r)
  -> (forall x. FSum cs x -> (x -> Node cs m a) -> r)
  -> (forall x. m x -> (x -> Node cs m a) -> r)
  -> Node cs m a
  -> r
{-# INLINE[0] unconsNode #-}
unconsNode ret _ _ (Pure a) = ret a
unconsNode _ con eff (Impure i k) =
  case i of
    InL e -> eff e cont
    InR c -> con c cont
  where
    cont = unconsCat runKleisli loop k
    loop ::
         Kleisli (Node cs m) y x
      -> Cat (Kleisli (Node cs m)) x a
      -> y
      -> Node cs m a
    loop kl cat y =
      case runKleisli kl y of
        Pure x -> unconsCat runKleisli loop cat x
        Impure i' cat' -> Impure i' (Cat cat' cat)

-- | Fold a 'Node'
cata ::
      forall cs m a r.
      (a -> r)
   -> (forall x. FSum cs x -> (x -> r) -> r)
   -> (forall x. m x -> (x -> r) -> r)
   -> Node cs m a
   -> r
{-# INLINE cata #-}
cata algR algC algE = cata_ algR algC' algE'
  where
    algC' :: Coyoneda (FSum cs) r -> r
    algC' (Coyoneda f c) = algC c f
    algE' :: Coyoneda m r -> r
    algE' (Coyoneda f e) = algE e f

-- This entire Coyoneda dance is rather ridiculous, but,
-- unfortunately, either GHC currently cannot stomach what would be a
-- rank-3 type rule, or I just lack the ability to trick it into doing
-- that.  Luckily, hiding one 'forall' inside a Coyoneda allows the
-- rule to fire normally; in fact, in this variant, the rewrite rules
-- almost exactly mimic the list fold/build fusion, which hopefully
-- means some protection against accidental breakage.
cata_ ::
     forall cs m a r.
     (a -> r)
  -> (Coyoneda (FSum cs) r -> r)
  -> (Coyoneda m r -> r)
  -> Node cs m a
  -> r
{-# INLINE[0] cata_ #-}
cata_ algR algC algE = loop
  where
    loop :: Node cs m a -> r
    loop =
      unconsNode
        algR
        (\c cont -> algC (Coyoneda (loop . cont) c))
        (\e cont -> algE (Coyoneda (loop . cont) e))

buildCon :: Coyoneda (FSum cs) (Node cs m a) -> Node cs m a
{-# INLINE[0] buildCon #-}
buildCon (Coyoneda f cs) = Impure (InR cs) . Leaf . Kleisli $ f

buildEff :: Coyoneda m (Node cs m a) -> Node cs m a
{-# INLINE[0] buildEff #-}
buildEff (Coyoneda f m) = Impure (InL m) . Leaf . Kleisli $ f

build ::
     (forall r.
         (a -> r)
      -> (forall x. FSum cs x -> (x -> r) -> r)
      -> (forall x. m x -> (x -> r) -> r)
      -> r)
  -> Node cs m a
{-# INLINE build #-}
build n =
  build_
    (\ret con lft ->
       n
         ret
         (\c cont -> con (Coyoneda cont c))
         (\e cont -> lft (Coyoneda cont e)))

build_ ::
     (forall r. (a -> r) -> (Coyoneda (FSum cs) r -> r) -> (Coyoneda m r -> r) -> r)
  -> Node cs m a
{-# INLINE[1] build_ #-}
build_ f = f Pure buildCon buildEff

augment ::
     (forall r. (a -> r) -> (Coyoneda (FSum cs) r -> r) -> (Coyoneda m r -> r) -> r)
  -> (a -> Node cs m b)
  -> Node cs m b
{-# INLINE[1] augment #-}
augment n f = n f buildCon buildEff

{-# RULES
"cata/build"
  forall
    ret
    con
    lft
    (node :: forall r.
                 (a -> r)
              -> (Coyoneda (FSum cs) r -> r)
              -> (Coyoneda m r -> r)
              -> r).
  cata_ ret con lft (build_ node) = node ret con lft
"cata/augment"
  forall
    ret
    con
    lft
    (node :: forall r.
                 (a -> r)
              -> (Coyoneda (FSum cs) r -> r)
              -> (Coyoneda m r -> r)
              -> r)
    (f :: a -> Node cs m b).
  cata_ ret con lft (augment node f) = node (cata_ ret con lft . f) con lft
#-}

instance Functor (Node cs m) where
  fmap = liftM

instance Applicative (Node cs m) where
  pure x = build (\ret _ _ -> ret x)
  (<*>) = ap
  (*>) = (>>)

instance Monad (Node cs m) where
  (>>=) = bind_
  (>>) = bindConst_

bind_ :: Node cs m a -> (a -> Node cs m b) -> Node cs m b
{-# INLINE[0] bind_ #-}
bind_ (Pure x) f = f x
bind_ (Impure x k) f = Impure x (k |> Kleisli f)

bindConst_ :: Node cs m a -> Node cs m b -> Node cs m b
{-# INLINE bindConst_ #-}
bindConst_ x = bind_ x . const

{-# RULES
"bind_"[~1]
  forall n.
  bind_ n = augment (\ret con lft -> cata_ ret con lft n)
"uncata"[1]
  forall ret.
  cata_ ret buildCon buildEff = (`bind_` ret)
#-}

instance MonadTrans (Node cs) where
  lift eff = build (\ret _ lft -> lft eff ret)

instance MonadIO m => MonadIO (Node cs m) where
  liftIO = lift . liftIO

instance Fail.MonadFail m => Fail.MonadFail (Node cs m) where
  fail = lift . Fail.fail

-- | Lift a @catch@-like function from the base level to 'Node'.
liftCatch ::
     Applicative m
  => (m (Node cs m a) -> (e -> m (Node cs m a)) -> m (Node cs m a))
  -> Node cs m a
  -> (e -> Node cs m a)
  -> Node cs m a
liftCatch catchBase node handler =
  cata_
    Pure
    buildCon
    (\eff ->
       buildEff $ liftCoyoneda (lowerCoyoneda eff `catchBase` (pure . handler)))
    node

instance MonadError e m => MonadError e (Node cs m) where
  throwError = lift . throwError
  catchError = liftCatch catchError

-- | This instance is safe only if @'local' f@ in the base monad is a
-- proper monad morphism (see "Control.Monad.Morph" for details),
-- which it usually is.
instance MonadReader r m => MonadReader r (Node cs m) where
  ask = lift ask
  reader = lift . reader
  -- This relies on `local f` being proper monad morphism… which is
  -- unknowable, since mtl doesn't have any laws on its
  -- classes. *grumble*
  local f = unsafeHoist (local f)

-- | Both 'listen' and 'pass' accumulate intermediate results
-- strictly.
instance MonadWriter w m => MonadWriter w (Node cs m) where
  writer = lift . writer
  tell = lift . tell
  listen node =
    build
      (\ret con lft ->
         cata
           (curry ret)
           (\c cont w -> con c (`cont` w))
           (\eff cont w ->
              lft
                (listen eff)
                (\(x, w') ->
                   let !w'' = w `mappend` w'
                   in cont x w''))
           node
           mempty)
  pass node =
    build
      (\ret con lft ->
         cata
           (\(a, f) w -> lft (tell (f w)) (const (ret a)))
           (\c cont w -> con c (`cont` w))
           (\eff cont w ->
              lft
                (censor (const mempty) (listen eff))
                (\(x, w') ->
                   let !w'' = w `mappend` w'
                   in cont x w''))
           node
           mempty)

instance MonadState s m => MonadState s (Node cs m) where
  get = lift get
  put = lift . put
  state = lift . state

instance MonadRWS r w s m => MonadRWS r w s (Node cs m)

instance MonadBase b m => MonadBase b (Node cs m) where
  liftBase = lift . liftBase

instance MonadThrow m => MonadThrow (Node cs m) where
  throwM = lift . throwM

instance MonadCatch m => MonadCatch (Node cs m) where
  catch = liftCatch catch

instance MonadResource m => MonadResource (Node cs m) where
  liftResourceT = lift . liftResourceT

instance PrimMonad m => PrimMonad (Node cs m) where
  type PrimState (Node cs m) = PrimState m
  primitive = lift . primitive

instance MFunctor (Node cs) where
  hoist f = unsafeHoist f . observe

instance MMonad (Node cs) where
  embed f node =
    build
      (\ret con lft ->
         cata ret con (\eff cont -> cata cont con lft (f eff)) node)

-- | Same as 'hoist', but potentially unsafe when the function passed
-- is /not/ a proper monad morphism.
--
-- The problem is that, as mentioned on the top of the module, 'Node'
-- violates monad transformer laws, and while said violations should
-- make no visible difference for a proper monad morphism, a general
-- monad transformation /can/ notice it (e.g. by counting the number
-- of the times it is called).
--
-- This problem is avoided in 'MFunctor' instance of 'Node' by
-- transforming 'Node' in a ‘canonical’ form via 'observe' prior to
-- passing it to 'unsafeHoist'; this restores the monad transformer
-- laws, but incurs a performance penalty.
unsafeHoist :: (forall x. m x -> n x) -> Node cs m a -> Node cs n a
unsafeHoist f node = build (\ret con lft -> cata ret con (lft . f) node)

-- | Run the 'Node' until it either completes, or initiates
-- communication on one of its channels.
inspect ::
     Monad m => Node cs m a -> m (Either a (Coyoneda (FSum cs) (Node cs m a)))
inspect =
  unconsNode
    (pure . Left)
    (\c cont -> pure . Right $ Coyoneda cont c)
    (\eff cont -> eff >>= (inspect . cont))

-- | Build a 'Node' by unfolding from a seed.
unfold ::
     (b -> m (Either a (Coyoneda (FSum cs) b))) -- ^ Step function; return value
     -- of 'Left' implies termination, while 'Right' implies
     -- communication request.
  -> b -- ^ Initial seed.
  -> Node cs m a
unfold step seed =
  build
    (\ret con lft ->
       let loop z =
             lft
               (step z)
               (\case
                  Left a -> ret a
                  Right (Coyoneda cont c) -> con c (loop . cont))
       in loop seed)

-- | Transform 'Node' to a ‘canonical’ form, where monad transformer
-- laws hold structurally.
--
-- The ‘canonical’ form begins with and 'EffectF' layer, then
-- 'ConnectF' layers interleaved with 'EffectF' layers until, after
-- the final 'EffectF', comes 'ReturnF'.  This involves complete
-- reconstruction of the 'Node', and requires ‘dropping’ into the base
-- monad at every sneeze, so should not be done lightheartedly.
--
-- @
-- 'observe' = 'unfold' 'inspect'
-- @
observe :: Monad m => Node cs m r -> Node cs m r
observe = unfold inspect
