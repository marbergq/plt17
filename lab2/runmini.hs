import System.Environment (getArgs)
import System.Exit (exitFailure)

import AbsMini
import LexMini
import ParMini
import ErrM
import PrintMini

import TypeChecker
import Interpreter


-- driver

check :: String -> IO () 
check s = case pProgram (myLexer s) of
            Bad err  -> do putStrLn "SYNTAX ERROR"
                           putStrLn err
                           exitFailure 
            Ok  tree -> case typecheck tree of
                          Bad err -> do putStrLn "TYPE ERROR"
                                        putStrLn err
                                        exitFailure 
                          Ok _    -> do putStrLn $ "Type check ok. Tree:\n" ++ (printTree tree) ++ "\nInterpreter output:\n"
                                        interpret tree

main :: IO ()
main = do args <- getArgs
          case args of
            [file] -> readFile file >>= check
            _      -> do putStrLn "Usage: lab2 <SourceFile>"
                         exitFailure
