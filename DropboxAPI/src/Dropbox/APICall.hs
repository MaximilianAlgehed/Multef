{-# LANGUAGE OverloadedStrings #-}
module Dropbox.APICall where

import System.IO
import Network.HTTP.Simple
import Network.HTTP.Conduit (RequestBody(RequestBodyBS))
import qualified Data.ByteString as BS
import qualified Data.ByteString.Lazy as LBS
import Data.Aeson
import Control.Monad.Reader
import Control.Monad.Except

import Dropbox.Types
import Dropbox.Instances

type AuthToken    = BS.ByteString
type DropboxError = BS.ByteString

type Dropbox = ExceptT DropboxError (ReaderT AuthToken IO)

runDropbox :: Dropbox a -> AuthToken -> IO (Either DropboxError a)
runDropbox d t = runReaderT (runExceptT d) t

logErr :: (MonadIO m, Show a) => a -> m ()
logErr = liftIO . hPutStrLn stderr . show 

listFolder :: ListFolderRequest -- ^ Request
           -> Dropbox ListFolderReply
listFolder request = do
  token <- ask
  r <- liftIO $ parseRequest "POST https://api.dropboxapi.com"
  let req = setRequestPath "/2/files/list_folder"
          $ setRequestHeaders [ ("Authorization", "Bearer " `BS.append` token)
                              , ("Content-Type", "application/json") ]
          $ setRequestBodyJSON request
          $ r
  bs <- liftIO (getResponseBody <$> httpLBS req)
  maybe (logErr bs >> throwError (LBS.toStrict bs)) return (decode bs)

upload :: UploadRequest -- ^ Request
       -> BS.ByteString -- ^ File Contents
       -> Dropbox Entry
upload request contents = do
  token <- ask
  r <- liftIO $ parseRequest "POST https://content.dropboxapi.com"
  let req = setRequestPath "/2/files/upload"
          $ setRequestHeaders [ ("Authorization", "Bearer " `BS.append` token)
                              , ("Dropbox-API-Arg", LBS.toStrict (encode request))
                              , ("Content-Type", "application/octet-stream") ]
          $ setRequestBody (RequestBodyBS contents)
          $ r
  bs <- liftIO (getResponseBody <$> httpLBS req)
  maybe (logErr bs >> throwError (LBS.toStrict bs)) return (decode bs)

download :: BS.ByteString    -- ^ Path to file
         -> Dropbox BS.ByteString -- ^ File contents
download path = do
  token <- ask
  r <- liftIO $ parseRequest "POST https://content.dropboxapi.com"
  let req = setRequestPath "/2/files/download"
          $ setRequestHeaders [ ("Authorization", "Bearer " `BS.append` token)
                              , ("Dropbox-API-Arg", "{ \"path\":\"" `BS.append` path `BS.append` "\"}") ]
          $ r
  liftIO (LBS.toStrict . getResponseBody <$> httpLBS req)

delete :: BS.ByteString    -- ^ Path to file
       -> Dropbox Metadata
delete path = do
  token <- ask
  r <- liftIO $ parseRequest "POST https://api.dropboxapi.com"
  let req = setRequestPath "/2/files/delete_v2"
          $ setRequestHeaders [ ("Authorization", "Bearer " `BS.append` token)
                              , ("Content-Type", "application/json") ]
          $ setRequestBody (RequestBodyBS $ "{ \"path\":\"" `BS.append` path `BS.append` "\"}")
          $ r
  bs <- liftIO (getResponseBody <$> httpLBS req)
  maybe (logErr bs >> throwError (LBS.toStrict bs)) return (decode bs)

createFolder :: BS.ByteString  -- ^ Path
             -> Bool           -- ^ Autorename
             -> Dropbox Metadata
createFolder path rename = do
  token <- ask
  r <- liftIO $ parseRequest "POST https://api.dropboxapi.com"
  let arn = if rename then "true" else "false"
      req = setRequestPath "/2/files/create_folder_v2"
          $ setRequestHeaders [ ("Authorization", "Bearer " `BS.append` token)
                              , ("Content-Type", "application/json") ]
          $ setRequestBody (RequestBodyBS $ "{\"path\":\"" `BS.append` path `BS.append` "\",\"autorename\":" `BS.append` arn `BS.append` "}")
          $ r
  bs <- liftIO (getResponseBody <$> httpLBS req)
  maybe (logErr bs >> throwError (LBS.toStrict bs)) return (decode bs)
