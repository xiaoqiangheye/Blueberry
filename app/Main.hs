module Main (main) where

-- import Front.Parse (parse)
import Front.ParserM (parse)
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
                                                putStrLn ("Parsing the program: " ++ filename)
                                                let program = parse contents
                                                putStrLn "Dumping the program AST.."
                                                print program
                                                putStrLn "Type checking the program.."
                                                infer program [])



