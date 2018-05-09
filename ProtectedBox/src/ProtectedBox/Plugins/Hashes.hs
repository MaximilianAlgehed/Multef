module ProtectedBox.Plugins.Hashes where

import qualified Data.ByteString as BS
import           Data.ByteString.Char8 (pack, unpack)
import Control.DeepSeq
import Control.Monad
import Crypto.Hash.SHA256 as Crypto
import ProtectedBox.Plugin as FIO

data API = Hashes Int (Faceted String)

hashes :: Int -> BS.ByteString -> BS.ByteString
hashes n = foldr (.) id (replicate n Crypto.hash)

runFun :: API -> FIO ()
runFun (Hashes n tree) = void $ branchOn tree $ \s -> let v = unpack (hashes n (pack s)) in force v `seq` output $ v

hash :: Plugin API
hash = Plugin "hash" runFun
