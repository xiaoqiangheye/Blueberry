module Main (main) where

import Lib
-- import Front.Parse (parse)
import ParserM (parse)
import Front.Typecheck
import System.IO(withFile, IOMode(ReadMode), hGetContents, hPutStrLn, stderr)
import System.Exit(exitFailure)
import System.Environment(getArgs, getProgName)


main :: IO ()
main = do
   args <- getArgs
   case args of
        [filename] -> processFile filename


processFile :: String -> IO ()
processFile filename =
        do withFile filename ReadMode (\h -> do contents <- hGetContents h
                                                let program = parse contents
                                                print program
                                                infer program [])



