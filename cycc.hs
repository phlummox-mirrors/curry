-- $Id: cycc.hs 1777 2005-09-30 14:56:48Z wlux $
--
-- Copyright (c) 1999-2005, Wolfgang Lux
-- See LICENSE for the full license.

import Modules
import PathUtils
import Options
import Combined
import Error
import GetOpt
import IO
import Maybe
import System

main :: IO ()
main =
  do
    prog <- getProgName
    args <- getArgs
    curryImports <- catch (getEnv "CURRY_IMPORTS" >>= return . pathList)
                          (const (return []))
    cyc prog args curryImports

cyc :: String -> [String] -> [FilePath] -> IO ()
cyc prog args curryImports
  | Help `elem` opts = printUsage prog
  | null errs = processFiles cycOpts prog files
  | otherwise = badUsage prog errs
  where (opts,files,errs) = getOpt Permute options args
        cycOpts =
	  foldr selectOption defaultOptions{ importPath = curryImports } opts

printUsage :: String -> IO ()
printUsage prog =
  do
    putStrLn (usageInfo (unlines header) options)
    exitWith ExitSuccess
  where header = ["usage: " ++ prog ++ " [OPTION]... SCRIPT..."]

badUsage :: String -> [String] -> IO ()
badUsage prog errs =
  do
    mapM_ (putErr . mkErrorLine) errs
    putErrLn ("Try `" ++ prog ++ " --help' for more information")
    exitWith (ExitFailure 1)
  where mkErrorLine err = prog ++ ": " ++ err

processFiles :: Options -> String -> [String] -> IO ()
processFiles opts prog files =
  case typeIt opts of
    Just g
      | isJust (goal opts) ->
          badUsage prog ["only one of -e and -t must be specified\n"]
      | length files > 1 ->
          badUsage prog ["cannot specify -t with multiple input files\n"]
      | otherwise -> compile (typeGoal opts g (listToMaybe files))
    Nothing ->
      case goal opts of
        Just g
          | isNothing (output opts) ->
              badUsage prog ["must specify -e with an output file\n"]
          | length files > 1 ->
              badUsage prog ["cannot specify -e with multiple input files\n"]
          | otherwise -> compile (compileGoal opts g (listToMaybe files))
	Nothing
          | null files -> badUsage prog ["no input files\n"]
          | isJust (output opts) && length files > 1 ->
              badUsage prog ["cannot specify -o with multiple input files\n"]
          | otherwise -> mapM_ (compile . compileModule opts) files

compile :: ErrorT IO a -> IO a
compile c = callErr c >>= checkOk
  where checkOk (Ok x) = return x
        checkOk (Error msg) = putErrLn msg >> exitWith (ExitFailure 1)

putErr, putErrLn :: String -> IO ()
putErr = hPutStr stderr
putErrLn = hPutStr stderr . (++ "\n")
