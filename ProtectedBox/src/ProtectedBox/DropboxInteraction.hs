{-# LANGUAGE OverloadedStrings #-}
module ProtectedBox.DropboxInteraction where

import Control.Monad.Reader
import Control.Concurrent
import Control.Concurrent.MVar
import Data.Maybe
import Text.Read
import qualified Data.ByteString as BS
import Data.ByteString.Char8 (pack, unpack)
import Control.Monad.Except
import Control.Monad.Trans
import Control.Monad
import System.FilePath
import Dropbox hiding (logErr)

import ProtectedBox.FIO

import System.IO

logErr = liftIO . hPutStr stderr . (++"\n")

-------------------------------
-- View-based file interface --
-------------------------------
-- Upload (write) to a file
maybeUploadViewWithPriv :: [Branch]
                        -> String
                        -> BS.ByteString
                        -> String
                        -> Dropbox ()
maybeUploadViewWithPriv pc name contents priv = do
  -- Get the label of the file
  lab <- unpack <$> download (pack $ name ++ ".fac")
  let mlabel = readMaybe lab
  when (isNothing mlabel) $ do
    logErr $ name ++ ".fac not found when using maybeUploadViewWithPriv"
    throwError "File not found"
  let Just label = mlabel

  -- If the current PC can write to the file,
  -- write the contents projected to the view
  when (label `inViewsOf` pc) $ do -- Here we should be using `priv` no?
    upload (defaultUploadRequest { upl_path = name, upl_mode = Overwrite }) contents
    return ()

uploadUnfaceted :: String
                -> BS.ByteString
                -> Dropbox ()
uploadUnfaceted name contents = do
  upload (defaultUploadRequest { upl_path = name, upl_mode = Overwrite }) contents
  return ()

-- Download a file
downloadView :: String
             -> Dropbox (Faceted (Maybe BS.ByteString))
downloadView name = flip catchError (\ _ -> return (Raw Nothing)) $ do
  -- Get the contents of the folder
  let (dot_path, fname) = splitFileName name
  let path = drop 1 dot_path
  listing <- listFolder $ defaultListFolder { lfr_path = if path == "/" then "" else path }
  let files = map entryName . filter (\e -> entryType e == File) $ entries listing

  -- If the correct files are not there, throw an error
  when (fname `notElem` files || (fname ++ ".fac") `notElem` files) $ do
    logErr (fname ++ " not found")
    throwError "File not found"
  
  -- Get the view associated with the file
  labelMVar <- liftIO $ newEmptyMVar
  token <- ask
  liftIO . forkIO . void . flip runDropbox token $ do
    label <- read . unpack <$> download (pack $ name ++ ".fac")
    liftIO $ putMVar labelMVar label

  -- Get the contents of the file
  contents <- download (pack name)
  label <- liftIO $ readMVar labelMVar

  -- Adapt the contents returned to the label 
  return $ facet label (raw $ Just contents) (raw Nothing)

downloadUnfaceted :: String
                  -> Dropbox (Faceted (Maybe BS.ByteString))
downloadUnfaceted name = flip catchError (\ _ -> return (Raw Nothing)) $ do
  -- Get the contents of the folder
  let (dot_path, fname) = splitFileName name
  let path = drop 1 dot_path
  listing <- listFolder $ defaultListFolder { lfr_path = if path == "/" then "" else path }
  let files = map entryName . filter (\e -> entryType e == File) $ entries listing

  -- If the correct files are not there, throw an error
  when (fname `notElem` files) $ do
    logErr $ "Couldn't find " ++ fname ++ " when trying to downloadUnfaceted"
    throwError "File not found"
  
  -- Get the contents of the file
  contents <- download (pack name)

  -- Adapt the contents returned to the label 
  return $ Raw (Just contents)

-- Create a new file with an attached label 
createFileLabel :: DCLabel
                -> String
                -> BS.ByteString
                -> Dropbox ()
createFileLabel label name contents = flip catchError (\ e -> return ()) . void $ do
  let (dot_path, fname) = splitFileName name
  let path = drop 1 dot_path
  listing <- listFolder $ defaultListFolder { lfr_path = if path == "/" then "" else path }
  let files = map entryName . filter (\e -> entryType e == File) $ entries listing
  when (fname `elem` files || (fname ++ ".fac") `elem` files) $ do
    logErr $ fname ++ " or " ++ fname ++ ".fac already exists when using createFileLabel"
    throwError "File already exists!"

  -- Create the view
  done <- liftIO newEmptyMVar
  token <- ask
  liftIO . forkIO . void . flip runDropbox token $ do
    upload (defaultUploadRequest { upl_path = name ++ ".fac" }) (pack $ show label)
    liftIO $ putMVar done ()
  -- Create the file
  upload (defaultUploadRequest { upl_path = name }) contents
  liftIO $ readMVar done

-- Create a new file with an attached label 
createFile :: String
           -> BS.ByteString
           -> Dropbox ()
createFile name contents = flip catchError (\ e -> return ()) . void $ do
  let (dot_path, fname) = splitFileName name
  let path = drop 1 dot_path
  listing <- listFolder $ defaultListFolder { lfr_path = if path == "/" then "" else path }
  let files = map entryName . filter (\e -> entryType e == File) $ entries listing
  when (fname `elem` files) $ do
    logErr $ fname ++ " already exists"
    (throwError "File already exists!")
  -- Create the file
  upload (defaultUploadRequest { upl_path = name }) contents
