{-# LANGUAGE DeriveDataTypeable #-}
{-# OPTIONS_GHC -fno-cse #-}
module Main where

import System.IO
import System.Console.CmdArgs
import System.Environment

import Data.List(stripPrefix)

data Opts
  = Expand { infile  :: FilePath
           , outfile :: Maybe FilePath
           }
  | Help
  deriving (Show, Data, Typeable)
           
expand :: Opts
expand = Expand
  { infile  = def &= args
                  &= typ "FILE"
  , outfile = def &= name "output"
                  &= explicit
                  &= typ "FILE"
                  &= help "Output file. stdout by default."
  }
  
mhelp :: Opts
mhelp = Help &= help "Display Help"
  
mode :: Mode (CmdArgs Opts)
mode = cmdArgsMode $ modes [expand &= auto, mhelp]
     &= help     "LaTeX \\include expansion."
     &= summary  "latex-include-expand\nVictor Miraldo<victor.cacciari@gmail.com>"

showHelp :: IO ()
showHelp = do
  _ <- withArgs ["--help"] $ cmdArgsRun mode
  return ()
  
getOpts :: IO Opts
getOpts = getArgs >>= doGetOpts
  where
    doGetOpts as
      | null as    = withArgs ["--help"] $ cmdArgsRun mode
      | otherwise  = cmdArgsRun mode
      
main :: IO ()
main = do
  opts <- getOpts
  case opts of
    Help         -> showHelp
    
    (Expand i Nothing) 
                 -> withFile i ReadMode (\hi -> doExpand hi stdout)
                 
    (Expand i (Just o)) 
                 -> withFile i ReadMode (\hi ->
                    withFile o WriteMode (\ho -> doExpand hi ho))
                    
doExpand :: Handle -> Handle -> IO ()      
doExpand hi ho
  = do
    eof <- hIsEOF hi
    if eof
    then return ()
    else hGetLine hi >>= processTo ho >> doExpand hi ho
  where
    processTo :: Handle -> String -> IO ()
    processTo ho str
      = case stripPrefix "\\include{" str of
            Nothing -> hPutStrLn ho str 
            Just s  -> readFile (takeWhile (/= '}') s) 
                   >>= hPutStrLn ho   

