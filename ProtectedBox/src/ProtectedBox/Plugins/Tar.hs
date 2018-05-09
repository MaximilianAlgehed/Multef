{-# LANGUAGE OverloadedStrings #-}
module ProtectedBox.Plugins.Tar where

import qualified Data.ByteString as BS
import           Data.ByteString.Char8 (pack, unpack)
import           Data.ByteString.Lazy (fromStrict, toStrict)
import Data.List
import Control.Monad
import ProtectedBox.Plugin as FIO

data API = Tar DCLabel [String] String

tar :: Plugin API
tar = Plugin "txt" runFun

files :: [String] -> ([(String, BS.ByteString)] -> FIO ()) -> FIO ()
files xs f = go [] xs
  where
    go ys []     = f ys
    go ys (x:xs) = do
      m_file <- FIO.readFile x 
      void $ branchOn m_file $ \m_contents ->
        case m_contents of
          Nothing       -> return ()
          Just contents -> go ((x, contents):ys) xs

makeTarball :: [(String, BS.ByteString)] -> BS.ByteString 
makeTarball fs = pack $ unlines [ s ++ ": " ++ unpack c | (s, c) <- fs ]

runFun :: API -> FIO ()
runFun api = case api of
  Tar label inputs target -> void $ do
    files inputs $ FIO.createFile label (target ++ ".txt") . makeTarball
