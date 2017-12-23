{-|
Module: Cobweb.Duplex
Description: Duplex communications, coroutine style.
Copyright: 2017 © Ivan Timokhin
License: BSD3
Maintainer: timokhin.iv@gmail.com
Stability: experimental

Duplex communications, as provided in this module and supporting
section in "Cobweb.Link", work on a request-response model.

That is, at each moment, one of the two communicating nodes is
blocked, waiting for data from the other.  The other node, which is
currently running, provides that data by making a request to the first
node, and blocks, waiting for a response.  Now the first node, which
has received the data it was waiting for, unblocks.  It then runs
until it makes a request to the second node, providing it the data
that it was waiting for, and blocking.  And so on.

Now, while this description is entirely correct for the case of
'Yield'/'Await' interface, provided by this module as 'Request',
"Cobweb.Link" in fact allows a more generic duplex interface, with
arbitrary functors for requests and responses.  Schematically, the
resulting control flow looks like this:

@
   .   .   .                        .    .    .
|  connectOn   |                     do stuff
|              |                 ________________
|_____________ lreq ---><--- rresp              |
                                 |              |
    do stuff                     |  connectOn   |
________________                 |              |
|              lresp ---><--- rreq______________|
|              |
|  connectOn   |                     do stuff
   .   .   .                       .    .    .
@

Note that now the channel consists of /two/ connection functors—for
request and response—which are combined via 'Compose'.
-}
{-# OPTIONS_HADDOCK show-extensions #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE ScopedTypeVariables #-}

module Cobweb.Duplex where

import Control.Monad ((>=>))
import Control.Monad.Trans (lift)

import Cobweb.Core
  ( Client
  , Node
  , Proxy
  , Request(Request)
  , connectOn
  , gforOn
  , i0
  , i1
  )
import Cobweb.Type.Combinators (Append, IIndex, Inductive, Remove)

-- | Send a request on the channel with a specified index.
requestOn :: Inductive cs => IIndex n cs (Request a b) -> a -> Node cs m b
requestOn n x = connectOn n (Request x)

-- | Use the provided function to serve incoming requests.
--
-- The type is set up so that this function with "Cobweb.Link" duplex
-- linking functions; e.g. as a first argument to
-- @('Cobweb.Link.+>>')@ or second to @('Cobweb.Link.>>~')@.
serve :: Monad m => (a -> m b) -> a -> Client b a m r
serve f = loop
  where
    loop a = do
      b <- lift (f a)
      a' <- requestOn i0 b
      loop a'

-- | Identity for the @('Cobweb.Link.>~>')@ composition operator; that
-- is,
--
-- @
-- node 'Cobweb.Link.>~>' 'push' = 'push' 'Cobweb.Link.>~>' node = node
-- @
--
-- The following diagram shows the flow of data (it loops
-- indefinitely).
--
-- @
--               a
--               |
--      +--------+--------+
--      |        |        |
--      |        \\==========> a
--      |                 |
--      |   'requestOn' 'i1'  |
--      |                 |
--      |        /==========< a'
--      |        |        |
--      +--------+--------+
--               |
--      +--------+--------+
--      |        |        |
-- a' <==========/        |
--      |                 |
--      |   'requestOn' 'i0'  |
--      |                 |
--  a >==========\\        |
--      |        |        |
--      +--------+--------+
--               |
--              ...
-- @
push :: Monad m => a -> Proxy a' a a' a m r
push = loop
  where
    loop = requestOn i1 >=> requestOn i0 >=> loop

-- | Identity for the @('Cobweb.Link.>+>')@ composition operator; that
-- is,
--
-- @
-- node 'Cobweb.Link.>+>' 'pull' = 'pull' 'Cobweb.Link.>+>' node = node
-- @
--
-- The following diagram shows the flow of data (it loops
-- indefinitely).
--
-- @
--               a'
--               |
--      +--------+--------+
--      |        |        |
-- a' <==========/        |
--      |                 |
--      |   'requestOn' 'i0'  |
--      |                 |
--  a >==========\\        |
--      |        |        |
--      +--------+--------+
--               |
--      +--------+--------+
--      |        |        |
--      |        \\==========> a
--      |                 |
--      |   'requestOn' 'i1'  |
--      |                 |
--      |        /==========< a'
--      |        |        |
--      +--------+--------+
--               |
--              ...
-- @
pull :: Monad m => a' -> Proxy a' a a' a m r
pull = loop
  where
    loop = requestOn i0 >=> requestOn i1 >=> loop

-- | A generalisation of 'push'; instead of simply passing values back
-- and forth, apply monadic transformation in transit.
--
-- The data flow for @'pushProxy' fwd bwd@ looks like this:
--
-- @
--               a
--               |
--              fwd
--               |
--      +--------+--------+
--      |        |        |
--      |        \\==========> b
--      |                 |
--      |   'requestOn' 'i1'  |
--      |                 |
--      |        /==========< b'
--      |        |        |
--      +--------+--------+
--               |
--              bwd
--               |
--      +--------+--------+
--      |        |        |
-- a' <==========/        |
--      |                 |
--      |   'requestOn' 'i0'  |
--      |                 |
--  a >==========\\        |
--      |        |        |
--      +--------+--------+
--               |
--              fwd
--               |
--              ...
-- @
pushProxy :: Monad m => (a -> m b) -> (b' -> m a') -> a -> Proxy a' a b' b m r
pushProxy fwd bwd = loop
  where
    loop =
      (lift . fwd) >=> requestOn i1 >=> (lift . bwd) >=> requestOn i0 >=> loop

-- | A generalisation of 'pull'; instead of simply passing values back
-- and forth, apply monadic transformation in transit.
--
-- The data flow for @'pullProxy' fwd bwd@ looks like this:
--
-- @
--               b'
--               |
--              bwd
--               |
--      +--------+--------+
--      |        |        |
-- a' <==========/        |
--      |                 |
--      |   'requestOn' 'i0'  |
--      |                 |
--  a >==========\\        |
--      |        |        |
--      +--------+--------+
--               |
--              fwd
--               |
--      +--------+--------+
--      |        |        |
--      |        \\==========> b
--      |                 |
--      |   'requestOn' 'i1'  |
--      |                 |
--      |        /==========< b'
--      |        |        |
--      +--------+--------+
--               |
--              bwd
--               |
--              ...
-- @
pullProxy :: Monad m => (a -> m b) -> (b' -> m a') -> b' -> Proxy a' a b' b m r
pullProxy fwd bwd = loop
  where
    loop =
      (lift . bwd) >=> requestOn i0 >=> (lift . fwd) >=> requestOn i1 >=> loop

-- | Iterate over specified duplex channel, replacing calls to
-- 'requestOn' with the loop body.
forOnDuplex ::
     forall n cs ocs cs' rescs a b m r. (Remove n cs ocs, Append ocs cs' rescs)
  => IIndex n cs (Request a b) -- ^ Index of the channel.
  -> Node cs m r
  -> (a -> Node cs' m b) -- ^ Replacement for 'requestOn'.
  -> Node rescs m r
forOnDuplex n node f = gforOn n node body
  where
    body :: Request a b x -> Node cs' m x
    body (Request a) = f a
