{-# LANGUAGE OverloadedStrings #-}
module ProtectedBox.Plugins.GZip where

import qualified Data.ByteString as BS
import           Data.ByteString.Char8 (pack, unpack)
import           Data.ByteString.Lazy (fromStrict, toStrict)
import Data.List
import Control.Monad
import Codec.Compression.GZip

import ProtectedBox.Plugin as FIO

data API = ZIP DCLabel String 

gzip :: Plugin API
gzip = Plugin "gz" runFun

runFun :: API -> FIO ()
runFun api = case api of
  ZIP label filename -> void $ do
    m_existingContents <- FIO.readFile filename
    branchOn m_existingContents $ \m_contents ->
      case m_contents of
        Just contents -> do
          m_existingZip <- FIO.readFile (filename ++ ".gz")
          let zipped = toStrict . compress . fromStrict $ contents
          branchOn m_existingZip $ maybe
                                    (FIO.createFile label (filename ++ ".gz") zipped)
                                    (\_ -> FIO.writeFile (filename ++ ".gz") zipped)
          output "Zipped"
        Nothing       -> output "No such file!"
