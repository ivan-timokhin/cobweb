{-# LANGUAGE TemplateHaskell #-}
{-# OPTIONS_GHC -O2 -fplugin Test.Inspection.Plugin #-}
module Main where

import Test.Inspection (inspect, hasNoType)
import Cobweb.Core (run, Node)
import Control.Monad.Trans (lift)

main :: IO ()
main = pure ()

runLift :: IO ()
runLift = run $ lift $ pure ()

inspect $ 'runLift `hasNoType` ''Node
