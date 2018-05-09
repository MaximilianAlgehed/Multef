{-# LANGUAGE GADTs #-}
module ProtectedBox.Plugin ( Plugin (..)
                           , sequencePlugin
                           , executeUNF 
                           , executeTINI
                           , executeSME
                           , executeFSME
                           , FIO
                           , FIO.Faceted
                           , FIO.writeFile
                           , FIO.readFile
                           , FIO.createFile
                           , FIO.output
                           , FIO.branchOn
                           , FIO.raw
                           , FIO.facet
                           , FIO.DCLabel(..)
                           , FIO.Form(..) ) where

import Dropbox
import Control.Concurrent.STM.TChan
import Control.Monad.STM
import Control.Monad
import Control.Concurrent.MVar
import Data.IORef

import ProtectedBox.FIO as FIO
import ProtectedBox.TINI
import ProtectedBox.UNF
import ProtectedBox.SME
import ProtectedBox.FSME

data Plugin a = Plugin { name :: String, run :: a -> FIO ()}

sequencePlugin :: Plugin a -> Plugin [a]
sequencePlugin (Plugin n rf) = Plugin n (mapM_ rf)

executeTINI :: Plugin a
            -> AuthToken
            -> String
            -> a 
            -> IO [([Branch], String)]
executeTINI plugin token user input = do
  chan <- atomically $ newTChan
  let pc = []
  flip runDropbox token $ tini (run plugin input) pc chan (name plugin) user
  getStuffFrom chan
  where
    getStuffFrom ch = do
      empty <- atomically $ isEmptyTChan ch
      if empty
      then return []
      else do
        v <- atomically $ readTChan ch
        (v:) <$> getStuffFrom ch

executeUNF :: Plugin a
            -> AuthToken
            -> String
            -> a 
            -> IO [([Branch], String)]
executeUNF plugin token user input = do
  chan <- atomically $ newTChan
  let pc = []
  flip runDropbox token $ unf (run plugin input) pc chan (name plugin) user
  getStuffFrom chan
  where
    getStuffFrom ch = do
      empty <- atomically $ isEmptyTChan ch
      if empty
      then return []
      else do
        v <- atomically $ readTChan ch
        (v:) <$> getStuffFrom ch

executeSME :: Plugin a
           -> AuthToken
           -> String
           -> a 
           -> IO [([Branch], String)]
executeSME plugin token user input = do
  chan <- atomically $ newTChan
  done <- newEmptyMVar :: IO (MVar ())
  counter <- newIORef 1
  let pc = []
  flip runDropbox token $ sme (run plugin input) pc chan (name plugin) user
                          counter done
  v <- atomicModifyIORef counter $ \v -> (v-1, v-1)
  when (v == 0) (putMVar done ())
  -- ***** Technically termination leaky! *****
  -- Used only for benchmarking!
  takeMVar done
  getStuffFrom chan
  where
    getStuffFrom ch = do
      empty <- atomically $ isEmptyTChan ch
      if empty
      then return []
      else do
        v <- atomically $ readTChan ch
        (v:) <$> getStuffFrom ch

executeFSME :: Plugin a
           -> AuthToken
           -> String
           -> a 
           -> Int
           -> IO [([Branch], String)]
executeFSME plugin token user input waitTime = do
  chan <- atomically $ newTChan
  done <- newEmptyMVar :: IO (MVar ())
  counter <- newIORef 1
  let pc = []
  flip runDropbox token $ fsme (run plugin input) pc chan (name plugin) user
                          counter done waitTime
  v <- atomicModifyIORef counter $ \v -> (v-1, v-1)
  when (v == 0) (putMVar done ())
  -- ***** Technically termination leaky! *****
  -- Used only for benchmarking!
  takeMVar done
  getStuffFrom chan
  where
    getStuffFrom ch = do
      empty <- atomically $ isEmptyTChan ch
      if empty
      then return []
      else do
        v <- atomically $ readTChan ch
        (v:) <$> getStuffFrom ch
