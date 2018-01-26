{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE TemplateHaskell #-}
{-# OPTIONS_GHC -O2 -fplugin Test.Inspection.Plugin #-}

module Main where

import Cobweb.Core (Node, run, unfold)
import Control.Monad.Base (MonadBase(liftBase))
import Control.Monad.Catch (Exception, MonadThrow(throwM))
import Control.Monad.Except (ExceptT, throwError)
import qualified Control.Monad.Fail as Fail
import Control.Monad.Morph (embed)
import Control.Monad.Reader (ReaderT, ask, local, reader)
import Control.Monad.State.Class (MonadState(get, put, state))
import Control.Monad.Trans (lift, liftIO)
import Control.Monad.Writer.Class (MonadWriter, listen, pass, tell, writer)

import Test.Inspection (hasNoType, inspect)

main :: IO ()
main = pure ()

-- * Internal module

runLift :: IO ()
runLift = run $ lift $ pure ()

runLiftFMap :: IO ()
runLiftFMap = run $ id <$> lift (pure ())

runLiftFMapConst :: IO ()
runLiftFMapConst = run $ () <$ lift (pure ())

runPure :: IO ()
runPure = run $ pure ()

runAp :: IO ()
runAp = run $ pure id <*> pure ()

runApL :: IO ()
runApL = run $ pure () *> pure ()

runApR :: IO ()
runApR = run $ pure () <* pure ()

runBind :: IO ()
runBind =
  run $ do
    x <- lift $ pure ()
    lift $ putStrLn ""
    pure x

runBindConst :: IO ()
runBindConst = run $ lift (putStrLn "") >> lift (pure ())

runLiftIO :: IO ()
runLiftIO = run $ liftIO $ pure ()

runFail :: IO ()
runFail = run $ Fail.fail "Hello"

runThrowE :: ExceptT () IO ()
runThrowE = run $ throwError ()

runAsk :: ReaderT () IO ()
runAsk = run ask

runReader :: ReaderT () IO ()
runReader = run $ reader id

runLocal :: ReaderT () IO ()
runLocal =
  run $
  local id $ do
    ask
    reader id

runWriter :: MonadWriter String m => m Int
runWriter = run $ writer (0, "Hello")

runTell :: MonadWriter String m => m ()
runTell = run $ tell "Hello"

runListen :: MonadWriter String m => m (Int, String)
runListen =
  run $
  listen $ do
    tell "Hello"
    writer (0, " World")

runPass :: MonadWriter String m => m Int
runPass =
  run $
  pass $ do
    tell "Hello"
    writer ((), " World")
    pure (10, (++ "!"))

runGet :: MonadState Int m => m Int
runGet = run get

runPut :: MonadState Int m => Int -> m ()
runPut = run . put

runState :: MonadState s m => (s -> (a, s)) -> m a
runState = run . state

runLiftBase :: MonadBase b m => b a -> m a
runLiftBase = run . liftBase

runThrowM :: (Exception e, MonadThrow m) => e -> m a
runThrowM = run . throwM

runEmbed :: Monad m => m ()
runEmbed =
  run $
  embed
    (\e -> do
       _ <- lift e
       lift e) $ do
    lift $ pure ()
    pure ()

runUnfold :: Monad m => m ()
runUnfold = run $ unfold (pure . Left) ()

fmap concat $
  traverse inspect $
  map
    (`hasNoType` ''Node)
    [ 'runLift
    , 'runLiftFMap
    , 'runLiftFMapConst
    , 'runPure
    , 'runAp
    , 'runApL
    , 'runApR
    , 'runBind
    , 'runBindConst
    , 'runLiftIO
    , 'runFail
    , 'runThrowE
    , 'runAsk
    , 'runReader
    , 'runLocal
    , 'runWriter
    , 'runTell
    , 'runListen
    , 'runPass
    , 'runGet
    , 'runPut
    , 'runState
    , 'runLiftBase
    , 'runThrowM
    , 'runEmbed
    , 'runUnfold
    ]
