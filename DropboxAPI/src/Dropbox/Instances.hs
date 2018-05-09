{-# LANGUAGE OverloadedStrings, DeriveGeneric #-}
module Dropbox.Instances where

import Data.Aeson
import Data.Aeson.Types

import Dropbox.Types

instance FromJSON EntryType where
  parseJSON (String "file")   = return File
  parseJSON (String "folder") = return Folder
  parseJSON _                 = fail "invalid"

instance FromJSON Entry where
  parseJSON (Object v) = Entry <$> v .:? ".tag" .!= File
                               <*> v .: "name"
                               <*> v .: "id"
                               <*> v .: "path_lower"
                               <*> v .: "path_display"
  parseJSON _          = fail "invalid"

instance FromJSON ListFolderReply where
  parseJSON (Object v) = ListFolderReply <$> v .: "entries"
                                         <*> v .: "cursor"
                                         <*> v .: "has_more"
  parseJSON _          = fail "invalid"

instance ToJSON ListFolderRequest where
  toEncoding = genericToEncoding (defaultOptions { fieldLabelModifier = drop 4}) 

instance ToJSON UploadMode where
  toJSON Add        = String "add"
  toJSON Overwrite  = String "overwrite"
  toJSON (Update r) = object [ ".tag" .= ("update" :: String)
                             , "update" .= r ]

instance ToJSON UploadRequest where
  toEncoding = genericToEncoding (defaultOptions { fieldLabelModifier = drop 4})

instance FromJSON Metadata where
  parseJSON = genericParseJSON defaultOptions
