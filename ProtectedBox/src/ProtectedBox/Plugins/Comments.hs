{-# LANGUAGE OverloadedStrings #-}
module ProtectedBox.Plugins.Comments (comments, API(..)) where

import Debug.Trace
import qualified Data.ByteString as BS
import           Data.ByteString.Char8 (pack, unpack)
import Data.List
import Control.Monad

import ProtectedBox.Plugin as FIO

data API = Add DCLabel String String
         | Delete String Int
         | Get String

comments :: Plugin API
comments = Plugin "Comments" runFun

runFun :: API -> FIO ()
runFun api = case api of
  Add label filename comment -> void $ do
    let cfn = filename
    m_existingContents <- FIO.readFile $ cfn ++ ".meta.Comments"
    branchOn m_existingContents $ \m_contents ->
      case m_contents of
        Just comments -> FIO.writeFile (cfn ++ ".meta.Comments") $ BS.append comments (pack $ "\n" ++ comment)
        Nothing       -> FIO.createFile label (cfn ++ ".meta.Comments") $ pack comment

  Delete filename cnum -> void $ do
    let cfn = filename
    m_existingContents <- FIO.readFile $ cfn ++ ".meta.Comments"
    branchOn m_existingContents $ \m_contents ->
      case m_contents of
        Just comments -> FIO.writeFile (cfn ++ ".meta.Comments")
                                       (pack $
                                        unlines [ c
                                                | (i, c) <- zip [0..]
                                                                (lines $ unpack comments),
                                                  i /= cnum
                                                ])
        Nothing       -> return () 
  
  Get filename -> void $ do
    let cfn = filename
    m_existingContents <- FIO.readFile (cfn ++ ".meta.Comments")
    branchOn m_existingContents $ \m_contents -> 
      case m_contents of
        Just comments -> output $ "Comments:\n" ++ unlines [ show i ++ ". " ++ c ++ "\n\n"
                                                           | (i, c) <- zip [0..]
                                                                           (lines (unpack comments))
                                                           ]
        Nothing       -> output "No comments on file"
