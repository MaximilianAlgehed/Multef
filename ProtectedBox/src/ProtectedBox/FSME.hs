{-# LANGUAGE GADTs, OverloadedStrings #-}
module ProtectedBox.FSME where

import qualified Data.ByteString as BS
import Control.Concurrent.STM.TChan
import Control.Concurrent.MVar
import Control.Monad.STM
import Control.Monad.IO.Class
import Control.Concurrent
import Control.Monad
import Control.Monad.Reader
import Control.Monad.Except
import System.Timeout
import Control.DeepSeq
import Data.IORef

import Dropbox

import ProtectedBox.FIO
import ProtectedBox.DropboxInteraction

fsme :: FIO a                     -- ^ Computation
     -> [Branch]                 -- ^ PC
     -> TChan ([Branch], String) -- ^ Output
     -> String                   -- ^ Current Principal
     -> String                   -- ^ Superuser
     -> IORef Int
     -> MVar ()
     -> Int
     -> Dropbox (a, [Branch])

fsme (Done a) pc o l owner ctn mv wt = return (a, pc)

fsme (Branch (Raw fio) k) pc o l owner ctn mv wt = do
  (a, pc') <- fsme fio pc o l owner ctn mv wt
  fsme (k (Raw a)) pc o l owner ctn mv wt

fsme (Branch (Faceted p priv pub) k) pc o l owner ctn mv wt 
  | takePrivate pc p = fsme (Branch priv k) pc o l owner ctn mv wt
  | takePublic  pc p = fsme (Branch pub k)  pc o l owner ctn mv wt
  | otherwise = do
      token <- ask
      privResult <- liftIO $ newEmptyMVar
      privCont   <- liftIO $ newEmptyMVar
      liftIO $ atomicModifyIORef ctn (\v -> (v+1, ()))
      liftIO . forkIO $ do
        flip runDropbox token $ do
          -- Private facet interpretation
          (priv', pc') <- fsme (Branch priv return)
                                 (Private p : pc) o l owner ctn mv wt
          -- Send result using the MVar
          liftIO $ putMVar privResult  priv'
          -- Wait for what to do next
          switchSME <- liftIO $ readMVar privCont 
          when switchSME $ void (fsme (k priv') pc' o l owner ctn mv wt)
        v <- atomicModifyIORef ctn (\v -> (v-1, v-1))
        when (v == 0) (putMVar mv ())

      -- Public facet interpretation
      onTime <- liftIO $ timeout wt (readMVar privResult)

      case onTime of
         Just priv' -> do
           -- No need to switch to SME
           liftIO $ putMVar privCont False
           fsme (Branch pub (\publ' -> k (Faceted p priv' publ')))
                (Public p : pc)
                o l owner ctn mv wt

         Nothing -> do
           -- Switching to SME
           liftIO $ putMVar privCont True
           fsme (Branch pub k) (Public p : pc) o l owner ctn mv wt

fsme (Read n cont) pc o l owner ctn mv wt = do
  tr <- downloadView n
  fsme (cont tr) pc o l owner ctn mv wt

fsme (Write n c cont) pc o l owner ctn mv wt = do
  maybeUploadViewWithPriv pc n c l
  fsme cont pc o l owner ctn mv wt

fsme (Create lab n c cont) pc o l owner ctn mv wt = do
  when (lab `inViewsOf` pc) $ do 
    createFileLabel lab n c
  fsme cont pc o l owner ctn mv wt

fsme (Output s cont) pc o l owner ctn mv wt = do
  liftIO . atomically $ writeTChan o (pc, s)
  fsme cont pc o l owner ctn mv wt
