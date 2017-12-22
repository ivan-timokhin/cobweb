{-|
Module: Cobweb.Resource
Description: Resource management in cobweb.
Copyright: 2017 © Ivan Timokhin
License: BSD3
Maintainer: timokhin.iv@gmail.com
Stability: experimental

Resource management in @cobweb@ is done via a 'MonadResource' instance
for 'Node', backed by a 'ResourceT' monad transformer.

By itself, proper use of that instance prevents complete resource
leaks; that is, all resources will be released when 'ResourceT' block
exits (via 'runResourceT', or convenience function 'runNodeRes'), and
it is possible to release them early by using 'release' or
'withResource' family of functions.

However, since linking functions from "Cobweb.Link" terminate the
communication graph as soon as at least one of the 'Node's terminates,
not all of them will run to completion and get a chance to release
their resources.  This is not a problem if that graph is an entire
content of a 'ResourceT' section, since all resources will be released
after that anyway, but may pose a problem if it is only a part of a
larger computation—e.g. a @do@-block.

To solve that problem, this module provides support for nested
'ResourceT' blocks.  While it is not possible to run 'ResourceT' on
top of 'Node' directly, it /is/ possible to provide something close.
In particular, the 'nested' family of functions provide resource
safety by registering the cleanup of inner 'ResourceT' with the outer
one, but also cleans up all registered resources early if the inner
block exits cleanly (or via a small number of supported exception
mechanisms).  On top of them, 'region' family of functions is provided
to simplify usage within 'Node'.

The solution to the above problem, then, is to wrap each communication
graph that can allocate resources and is embedded in a @do@-block in
an appropriate 'nested' function.  This way, if the graph as a whole
exits cleanly, resources will be released promptly, and even if
something goes wrong, they will be released when the surrounding
'ResourceT' block exits.

As a final cautionary note, keep in mind that the functions in this
module work under assumption that the underlying monad does not
interleave effects; that is, in @('>>=')@, left argument runs to
completion before the right one is started.  While this is true of
/most/ monads, this is /not/ true of various @ListT@ implementations,
such as the one in "Cobweb.List", or the one in @pipes@, or the one in
@listt@.  These operate by building a gigantic nested loop, in which
later operations correspond to inner loops; releasing a resource
‘promptly’ in such setting would imply releasing it on a first
iteration of the loop, even though other iterations probably rely on
it.
-}
{-# OPTIONS_HADDOCK show-extensions #-}
{-# LANGUAGE FlexibleContexts #-}

module Cobweb.Resource
  ( runNodeRes
  -- * Node regions
  , region
  , regionC
  , regionE
  , regionCE
  -- * Nested 'ResourceT'
  , nested
  , nestedC
  , nestedE
  , nestedCE
  -- * 'withResource'
  , withResource
  , withResourceC
  , withResourceE
  , withResourceCE
  -- * Tutorial
  -- $tutorial
  ) where

import Control.Monad.Catch (MonadCatch, onException)
import Control.Monad.Error.Class
       (MonadError(catchError, throwError))
import Control.Monad.Trans.Resource
       (InternalState, MonadBaseControl, MonadResource, ResourceT,
        allocate, closeInternalState, createInternalState, release,
        runInternalState, runResourceT)

import Cobweb.Core (Effect, Node, run)
import Cobweb.Trans (distribute)

-- | A convenience function to run both 'Node' and 'ResourceT' in one
-- go.
runNodeRes :: MonadBaseControl IO m => Effect (ResourceT m) a -> m a
runNodeRes = runResourceT . run

-- | Set up a local resource registry for 'Node', cleaning it early if the
-- provided computation exits normally; otherwise, it will be cleaned
-- when outer 'ResourceT' exits.
region ::
     MonadResource m
  => Node cs (ResourceT m) a
  -> Node cs m a
region = nested . distribute

-- | Same as 'region', but also release resources early if the block
-- exits via a kind of exception that 'MonadCatch' instance can catch.
regionC ::
     (MonadResource m, MonadCatch m) => Node cs (ResourceT m) a -> Node cs m a
regionC = nestedC . distribute

-- | Same as 'region', but also release resources early if the block
-- exits via 'throwError'.
regionE ::
     (MonadResource m, MonadError e m) => Node cs (ResourceT m) a -> Node cs m a
regionE = nestedE . distribute

-- | Same as 'region', but also release resources early if the block
-- exits via exception that can be intercepted via 'MonadCatch' or
-- 'MonadError' instances.
regionCE ::
     (MonadResource m, MonadCatch m, MonadError e m)
  => Node cs (ResourceT m) a
  -> Node cs m a
regionCE = nestedCE . distribute

-- | Set up a local resource registry, cleaning it early if the provided
-- computation exits normally; otherwise, it will be cleaned when
-- outer 'ResourceT' exits.
--
-- Note that only the resources allocated via ‘outer’ 'ResourceT' will
-- be released early.
nested :: MonadResource m => ResourceT m a -> m a
nested = nestedGen withResource

-- | Same as 'nested', but also release resources early if the block
-- exits via a kind of exception that 'MonadCatch' instance can catch.
nestedC :: (MonadResource m, MonadCatch m) => ResourceT m a -> m a
nestedC = nestedGen withResourceC

-- | Same as 'nested', but also release resources early if the block
-- exits via 'throwError'.
nestedE :: (MonadResource m, MonadError e m) => ResourceT m a -> m a
nestedE = nestedGen withResourceE

-- | Same as 'nested', but also release resources early if the block
-- exits via exception that can be intercepted via 'MonadCatch' or
-- 'MonadError' instances.
nestedCE ::
     (MonadResource m, MonadCatch m, MonadError e m) => ResourceT m a -> m a
nestedCE = nestedGen withResourceCE

nestedGen ::
     (IO InternalState -> (InternalState -> IO ()) -> (InternalState -> m b) -> m b)
  -> ResourceT m b
  -> m b
nestedGen with = with createInternalState closeInternalState . runInternalState

-- | Run a computation with a given resource, both registering the
-- cleanup action via provided 'MonadResource' instance, and running
-- it early if the inner block exits normally.
withResource ::
     MonadResource m
  => IO a -- ^ Acquire resource.
  -> (a -> IO ()) -- ^ Release resource.
  -> (a -> m b) -- ^ Use resource.
  -> m b
withResource ini fin act = do
  (rk, res) <- allocate ini fin
  x <- act res
  release rk
  pure x

-- | Same as 'withResource', but also release resource early if the
-- block exits via a kind of exception that 'MonadCatch' instance can
-- catch.
withResourceC ::
     (MonadResource m, MonadCatch m)
  => IO a -- ^ Acquire resource.
  -> (a -> IO ()) -- ^ Release resource.
  -> (a -> m b) -- ^ Use resource.
  -> m b
withResourceC ini fin act = do
  (rk, res) <- allocate ini fin
  x <- act res `onException` release rk
  release rk
  pure x

-- | Same as 'withResource', but also release resource early if the
-- block exits via 'throwError'.
withResourceE ::
     (MonadResource m, MonadError e m)
  => IO a -- ^ Acquire resource.
  -> (a -> IO ()) -- ^ Release resource.
  -> (a -> m b) -- ^ Use resource.
  -> m b
withResourceE ini fin act = do
  (rk, res) <- allocate ini fin
  x <-
    act res `catchError` \e -> do
      release rk
      throwError e
  release rk
  pure x

-- | Same as 'withResource', but also release resource early if the
-- block exits via exception that can be intercepted via 'MonadCatch'
-- or 'MonadError' instances.
withResourceCE ::
     (MonadResource m, MonadCatch m, MonadError e m)
  => IO a -- ^ Acquire resource.
  -> (a -> IO ()) -- ^ Release resource.
  -> (a -> m b) -- ^ Use resource.
  -> m b
withResourceCE ini fin act = do
  (rk, res) <- allocate ini fin
  x <-
    (act res `onException` release rk) `catchError` \e -> do
      release rk
      throwError e
  release rk
  pure x

-- $tutorial
--
-- To illustrate resource handling in @cobweb@, let's start with a
-- simple example: copying files.
--
-- First, some helper functions to visualise control flow:
--
-- @
--
-- openFileLoud :: 'FilePath' -> 'System.IO.IOMode' -> 'IO' 'System.IO.Handle'
-- openFileLoud name mode = do
--   'Text.Printf.printf' "Opening file %s\\n" name
--   'System.IO.openFile' name mode
--
-- closeFileLoud :: 'FilePath' -> 'System.IO.Handle' -> 'IO' ()
-- closeFileLoud name handle = do
--   'Text.Printf.printf' "Closing file %s\\n" name
--   'System.IO.hClose' handle
--
-- @
--
-- Now, let's write a simple 'Cobweb.Producer.Producer' to read a
-- file, and 'Cobweb.Consumer.Consumer' to write it.  Since I can't be
-- bothered to manage my resources myself, I'll use 'withResource' to
-- handle that for me.  The interface is similar to
-- 'Control.Exception.bracket' (though there are important
-- differences, as we'll see later).
--
--
-- First, reading file:
--
-- @
-- readingFile :: 'MonadResource' m => 'FilePath' -> 'Cobweb.Producer.Producer' 'String' m ()
-- readingFile name =
--   'withResource' (openFileLoud name 'System.IO.ReadMode') (closeFileLoud name) $ \\handle ->
--     let loop :: 'MonadResource' m => 'Cobweb.Producer.Producer' 'String' m ()
--         loop = do
--           eof <- 'Control.Monad.IO.Class.liftIO' $ 'System.IO.hIsEOF' handle
--           'Contol.Monad.unless' eof $ do
--             str <- 'Control.Monad.IO.Class.liftIO' $ 'System.IO.hGetLine' handle
--             'Cobweb.Producer.yield' str
--             loop
--     in loop
-- @
--
-- Nothing surprising so far; we obtain a file handle via
-- 'withResource', and read lines from it until the end of file.
-- Moving on to writing:
--
-- @
-- writingFile :: 'MonadResource' m => 'FilePath' -> 'Cobweb.Consumer.Consumer' 'String' m ()
-- writingFile name =
--   'withResource' (openFileLoud name WriteMode) (closeFileLoud name) $ \\handle ->
--     let loop :: 'MonadResource' m => 'Cobweb.Consumer.Consumer' 'String' m ()
--         loop = do
--           str <- 'Cobweb.Consumer.await'
--           'Control.Monad.IO.Class.liftIO' $ 'System.IO.hPutStrLn' handle str
--           loop
--     in loop
-- @
--
-- Again, not exactly unexpected.  We get lines from upstream and
-- write them to the file.  A slightly surprising moment here, though,
-- is that we never /terminate/.  The reason for that is that we can
-- only run out of lines to write if the upstream terminates, and in
-- that case we'll get killed by the linking function anyway.
--
-- Armed with these, we can write our glorious copying function:
--
-- @
-- test1 :: 'IO' ()
-- test1 = 'runNodeRes' '$' readingFile \"a.txt\" 'Cobweb.Link.>->' writingFile \"b.txt\"
-- @
--
-- If you're following along, now would be a good time to create
-- @a.txt@ and fill it with some text (we'll need 6 lines).
--
-- Now you can run our @test1@, and see the following:
--
-- > Opening file b.txt
-- > Opening file a.txt
-- > Closing file a.txt
-- > Closing file b.txt
--
-- Very nice!  Both files got closed successfully, and if you open
-- @b.txt@, you should see the contents of @a.txt@, successfully
-- copied.
--
-- Let's spice things up a bit.  Instead of copying file entirely,
-- we'll copy five lines to one file, and the rest to another.  We can
-- try to do it like this:
--
-- @
-- test2 :: 'IO' ()
-- test2 = 'runNodeRes' '$' readingFile "a.txt" 'Cobweb.Link.>->' sink
--   where
--     sink = do
--       'Cobweb.Pipe.taking' 5 'Cobweb.Link.>->' writingFile "b.txt"
--       writingFile "c.txt"
-- @
--
-- And if you'll run that, you'll see…
--
-- > Opening file b.txt
-- > Opening file a.txt
-- > Opening file c.txt
-- > Closing file a.txt
-- > Closing file c.txt
-- > Closing file b.txt
--
-- Ouch!  Yes, all files got closed properly, but we clearly held onto
-- @b.txt@ for /much/ longer than we needed.  If you think for a
-- while, the reason should become clear: since @writingFile@ never
-- terminates by itself, it never closes the file, so it gets closed
-- only when 'ResourceT' block exits, i.e. at 'runNodeRes'.
--
-- Luckily, there's an easy solution for that problem.  What we need
-- is to setup a local resource registry /just/ for our first
-- @writingFile@ call, which will get cleaned immediately after.
-- That's /exactly/ what the 'region' family of functions does!
-- Here's how we'll use it:
--
-- @
-- test3 :: 'IO' ()
-- test3 = 'runNodeRes' '$' readingFile "a.txt" 'Cobweb.Link.>->' sink
--   where
--     sink = do
--       'region' '$' 'Cobweb.Pipe.taking' 5 'Cobweb.Link.>->' writingFile "b.txt" -- HERE
--       writingFile "c.txt"
-- @
--
-- Running that gives…
--
-- > Opening file b.txt
-- > Opening file a.txt
-- > Closing file b.txt
-- > Opening file c.txt
-- > Closing file a.txt
-- > Closing file c.txt
--
-- Hooray!  There are only two files open at any given moment, which
-- is exactly what we needed.
--
-- This, then, is a golden rule of resource management with @cobweb@:
--
-- @
-- Whenever you exit horizontally composed block without also
-- exiting 'ResourceT', wrap it in the most specific 'region' you can.
-- @
