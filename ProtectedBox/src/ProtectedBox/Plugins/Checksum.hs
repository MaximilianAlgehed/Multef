{-# LANGUAGE OverloadedStrings #-}
module ProtectedBox.Plugins.Checksum where

import qualified Data.ByteString as BS
import           Data.ByteString.Char8 (pack, unpack)
import Data.List
import Control.Monad
import Crypto.Hash.SHA256
import Data.ByteString.Base64

import ProtectedBox.Plugin as FIO

data API = SHA256 String 
         deriving (Ord, Eq, Show, Read)

checksum :: Plugin API
checksum = Plugin "Checksum" runFun

runFun :: API -> FIO ()
runFun api = case api of
  SHA256 filename -> void $ do
    m_existingContents <- FIO.readFile filename
    branchOn m_existingContents $ \m_contents ->
      case m_contents of
        Just contents -> output . ("Base 64 SHA256: "++) . unpack . encode . hash $ contents
        Nothing       -> output "File empty!"
