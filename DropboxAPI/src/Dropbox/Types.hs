{-# LANGUAGE DeriveGeneric #-}
module Dropbox.Types where

import GHC.Generics

data EntryType = File
               | Folder
               deriving (Ord, Eq, Show)

data Entry = Entry { entryType        :: EntryType
                   , entryName        :: String
                   , entryId          :: String
                   , entryPathLower   :: String
                   , entryPathDisplay :: String }
                   deriving (Ord, Eq, Show)

data ListFolderReply = ListFolderReply { entries  :: [Entry]
                                       , cursor   :: String
                                       , has_more :: Bool }
                                       deriving (Ord, Eq, Show)

data ListFolderRequest = ListFolderRequest { lfr_path                                :: String
                                           , lfr_recursive                           :: Bool
                                           , lfr_include_media_info                  :: Bool
                                           , lfr_include_deleted                     :: Bool
                                           , lfr_include_has_explicit_shared_members :: Bool
                                           , lfr_include_mounted_folders             :: Bool }
                                           deriving (Ord, Eq, Show, Generic)

defaultListFolder :: ListFolderRequest
defaultListFolder = ListFolderRequest "" False False False False True

data UploadMode = Add
                | Overwrite
                | Update { uplm_rev :: String }
                deriving (Ord, Eq, Show, Generic)

data UploadRequest = UploadRequest { upl_path       :: String
                                   , upl_mode       :: UploadMode
                                   , upl_autorename :: Bool
                                   , upl_mute       :: Bool }
                                   deriving (Ord, Eq, Show, Generic)

defaultUploadRequest :: UploadRequest
defaultUploadRequest = UploadRequest "" Add True False

data Metadata = Metadata { metadata :: Entry } deriving (Ord, Eq, Show, Generic)
