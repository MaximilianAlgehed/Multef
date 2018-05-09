{-# LANGUAGE GADTs, OverloadedStrings #-}
module ProtectedBox.SME where

import qualified Data.ByteString as BS
import Control.Concurrent.STM.TChan
import Control.Concurrent.MVar
import Control.Monad.STM
import Control.Monad.IO.Class
import Control.Concurrent
import Control.Monad
import Control.Monad.Reader
import Control.Monad.Except
import Data.IORef

import Dropbox

import ProtectedBox.FIO
import ProtectedBox.DropboxInteraction

sme :: FIO a                     -- ^ Computation
     -> [Branch]                 -- ^ PC
     -> TChan ([Branch], String) -- ^ Output
     -> String                   -- ^ Current Principal
     -> String                   -- ^ Superuser
     -> IORef Int
     -> MVar ()
     -> Dropbox (a, [Branch])

sme (Done a) pc o l owner ctn mv = return (a, pc)

sme (Branch (Raw fio) k) pc o l owner ctn mv = do
  (a, pc') <- sme fio pc o l owner ctn mv
  sme (k (Raw a)) pc o l owner ctn mv

sme (Branch (Faceted p priv pub) k) pc o l owner ctn mv
  | takePrivate pc p = sme (Branch priv k) pc o l owner ctn mv
  | takePublic  pc p = sme (Branch pub k)  pc o l owner ctn mv
  | otherwise = do
      token <- ask
      liftIO $ atomicModifyIORef ctn (\v -> (v+1, ()))
      liftIO . forkIO $ do
        flip runDropbox token $ sme (Branch priv k) (Private p : pc) o l owner ctn mv
        v <- liftIO $ atomicModifyIORef ctn (\v -> (v-1, v-1))
        when (v == 0) (putMVar mv ())
      sme (Branch pub k) (Public p : pc) o l owner ctn mv

sme (Read n cont) pc o l owner ctn mv = do
  tr <- downloadView n
  sme (cont tr) pc o l owner ctn mv

sme (Write n c cont) pc o l owner ctn mv = do
  maybeUploadViewWithPriv pc n c l
  sme cont pc o l owner ctn mv

sme (Create lab n c cont) pc o l owner ctn mv = do
  when (lab `inViewsOf` pc) $ do 
    createFileLabel lab n c
  sme cont pc o l owner ctn mv

sme (Output s cont) pc o l owner ctn mv = do
  liftIO . atomically $ writeTChan o (pc, s)
  sme cont pc o l owner ctn mv
