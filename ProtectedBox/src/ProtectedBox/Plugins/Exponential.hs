module ProtectedBox.Plugins.Exponential where

import qualified Data.ByteString as BS
import           Data.ByteString.Char8 (pack, unpack)
import Control.DeepSeq
import Control.Monad
import Crypto.Hash.SHA256 as Crypto
import ProtectedBox.Plugin as FIO
import ProtectedBox.FIO as FIOTCB

data API = ExpHashes Int (Faceted String) String

hashes :: Int -> BS.ByteString -> BS.ByteString
hashes n = foldr (.) id (replicate n Crypto.hash)

runFun :: API -> FIO ()
runFun (ExpHashes n tree h) = do
  f <- branchOn tree return
  let v = unpack (hashes n (pack (h ++ take 10 (printFaceted f)))) in v `seq` output v

expHash :: Plugin API
expHash = Plugin "expHash" runFun
