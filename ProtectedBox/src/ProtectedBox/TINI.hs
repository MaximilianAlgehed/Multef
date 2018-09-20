{-# LANGUAGE GADTs, OverloadedStrings #-}
module ProtectedBox.TINI where

import qualified Data.ByteString as BS
import Control.Concurrent.STM.TChan
import Control.Monad.STM
import Control.Monad.IO.Class
import Control.Concurrent
import Control.Monad
import Control.Monad.Reader

import Dropbox

import ProtectedBox.FIO
import ProtectedBox.DropboxInteraction

tini :: FIO a                    -- ^ Computation
     -> [Branch]                 -- ^ PC
     -> TChan ([Branch], String) -- ^ Output
     -> String                   -- ^ Plugin label
     -> String                   -- ^ Superuser
     -> Dropbox (a, [Branch])

tini (Done a) pc o l owner = return (a, pc)

tini (Branch (Raw fio) k) pc o l owner = do
  (a, pc') <- tini fio pc o l owner
  tini (k (Raw a)) pc o l owner

tini (Branch (Faceted p priv pub) k) pc o l owner
  | takePrivate pc p = tini (Branch priv k) pc o l owner
  | takePublic  pc p = tini (Branch pub k)  pc o l owner
  | otherwise = do
      (a1,_) <- tini (Branch priv return) (Private p : pc) o l owner
      (a2,_) <- tini (Branch pub return)  (Public p : pc) o l owner
      tini (k (Faceted p a1 a2)) pc o l owner

tini (Read n cont) pc o l owner = do
  tr <- downloadView n
  tini (cont tr) pc o l owner

tini (Write n c cont) pc o l owner = do
  maybeUploadViewWithPriv pc n c l
  tini cont pc o l owner

tini (Create lab n c cont) pc o l owner = do
  when (lab `inViewsOf` pc) (createFileLabel lab n c)
  tini cont pc o l owner

tini (Output s cont) pc o l owner = do
  liftIO . atomically $ writeTChan o (pc, s)
  tini cont pc o l owner
