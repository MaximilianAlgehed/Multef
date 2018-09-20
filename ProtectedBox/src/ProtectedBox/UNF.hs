{-# LANGUAGE GADTs
           , OverloadedStrings
#-}
module ProtectedBox.UNF where

import qualified Data.ByteString as BS
import Control.Concurrent.STM.TChan
import Control.Monad.STM
import Control.Monad.IO.Class
import Control.Concurrent
import Control.Monad
import Control.Monad.Reader

import Dropbox

import ProtectedBox.FIO hiding (createFile)
import ProtectedBox.DropboxInteraction

unf :: FIO a                    -- ^ Computation
    -> [Branch]                 -- ^ PC
    -> TChan ([Branch], String) -- ^ Output
    -> String                   -- ^ Plugin label
    -> String                   -- ^ Superuser
    -> Dropbox (a, [Branch])

unf (Done a) pc o l owner = return (a, pc)

unf (Branch (Raw fio) k) pc o l owner = do
  (a, pc') <- unf fio pc o l owner
  unf (k (Raw a)) pc o l owner

unf (Read n cont) pc o l owner = do
  tr <- downloadUnfaceted n 
  unf (cont tr) pc o l owner

unf (Write n c cont) pc o l owner = do
  uploadUnfaceted n c
  unf cont pc o l owner

unf (Create lab n c cont) pc o l owner = do
  createFile n c
  unf cont pc o l owner

unf (Output s cont) pc o l owner = do
  liftIO . atomically $ writeTChan o (pc, s)
  unf cont pc o l owner
