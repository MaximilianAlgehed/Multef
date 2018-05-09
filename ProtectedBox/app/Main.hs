{-# LANGUAGE OverloadedStrings #-}
module Main where

import System.Environment
import qualified Data.ByteString.Char8 as BS

import Dropbox (runDropbox, delete)

import ProtectedBox.DropboxInteraction
import ProtectedBox hiding (createFile)
import ProtectedBox.Plugins.Comments
import ProtectedBox.Plugins.Tar
import ProtectedBox.Plugins.Hashes
import ProtectedBox.Plugins.Exponential

-- The comments benchmark
commentsBM :: IO ()
commentsBM = do 
  [_, len, token, method] <- getArgs
  let l = read len :: Int
  let input = [ Add (DCLabel (Atomic "Max") (Atomic "Max")) "/hello.txt" "hello" | i <- [1..l] ]
  runDropbox (uploadUnfaceted "/hello.txt.meta.Comments" "") (BS.pack token)
  case method of
    "unf"  -> executeUNF  (sequencePlugin comments) (BS.pack token) "Max" input
    "tini" -> executeTINI (sequencePlugin comments) (BS.pack token) "Max" input
    "sme"  -> executeSME  (sequencePlugin comments) (BS.pack token) "Max" input
    "fsme" -> executeFSME (sequencePlugin comments) (BS.pack token) "Max" input 15000000
  return ()

-- The tarball benchmark
tarballBM :: IO ()
tarballBM = do 
  [_, len, token, method] <- getArgs
  let l = read len :: Int
  let label = foldl1 lub [ DCLabel (Atomic $ show i) (Atomic $ show i) | i <- [1..l] ]
  let input = Tar label [ "/hello" ++ show i | i <- [1..l] ] "/tarball"
  runDropbox (delete "/tarball.txt") (BS.pack token)
  runDropbox (delete "/tarball.txt.fac") (BS.pack token)
  case method of
    "unf"  -> executeUNF  tar (BS.pack token) "Max" input
    "tini" -> executeTINI tar (BS.pack token) "Max" input
    "sme"  -> executeSME  tar (BS.pack token) "Max" input
    "fsme" -> executeFSME tar (BS.pack token) "Max" input 15000000
  return ()

tarballPrepare :: IO ()
tarballPrepare = do
  [_, len, token] <- getArgs
  let l = read len :: Int
  let files = [ (DCLabel (Atomic $ show i) (Atomic $ show i), "/hello" ++ show i) | i <- [1..l] ]
  runDropbox (sequence_ [createFile (f ++ ".fac") (BS.pack $ show l) | (l, f) <- files] ) (BS.pack token)
  runDropbox (sequence_ [createFile f "helloThere" | (l, f) <- files] ) (BS.pack token)
  return ()

hashesBM :: IO ()
hashesBM = do
  [_, sizeS, args, method] <- getArgs
  let size = read sizeS :: Int
  let [number, timeout] = read args :: [Int]
  let input = Hashes number (foldr (\l f -> facet l f f) (raw "hello") [ DCLabel (Atomic $ show i) (Atomic $ show i) | i <- [1..size] ])
  case method of
    "unf"  -> executeUNF  hash (BS.pack "") "Max" input
    "tini" -> executeTINI hash (BS.pack "") "Max" input
    "sme"  -> executeSME  hash (BS.pack "") "Max" input
    "fsme" -> executeFSME hash (BS.pack "") "Max" input timeout 
  return ()

expHashesBM :: IO ()
expHashesBM = do
  [_, sizeS, numS, method] <- getArgs
  let size = read sizeS :: Int
  let number = read numS :: Int
  let input = ExpHashes number (foldr (\l f -> facet l f f) (raw "hello") [ DCLabel (Atomic $ show i) (Atomic $ show i) | i <- [1..size] ])
                               "hello"
  case method of
    "tini" -> executeTINI expHash (BS.pack "") "Max" input
    "sme"  -> executeSME  expHash (BS.pack "") "Max" input
    "fsme"  -> executeFSME  expHash (BS.pack "") "Max" input 1500000
  return ()

main :: IO ()
main = do 
  bm <- head <$> getArgs
  case bm of
    "expHashes"       -> expHashesBM
    "hashes"          -> hashesBM
    "comments"        -> commentsBM
    "tarball"         -> tarballBM
    "tarball-prepare" -> tarballPrepare
  return ()
