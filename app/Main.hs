module Main where

import Control.Monad
import System.Environment (getArgs)
import System.IO (hGetContents)
import Ast
import Core (isNumericValue, genTypeVarsProg, int_of_nat)
import Interp (interpProg)
import Parser (parseProg)
import Preprocessor (importLines, substImports)
import Tycheck (tycheckProg, runTycheck)

main :: IO ()
main = do
  args <- getArgs

  -- Read in source file
  src <- readFile $ case args of
                      [f] -> f
                      []  -> error "Error: no input file"
  -- Locate import commands
  let imports = importLines (lines src)

  -- Map imports to their corresponding source code
  import_srcs <- mapM
    (\(lnum, imps) ->
        sequence (lnum, (mapM (readFile . (++ ".cf")) imps)))
    imports

  -- Replace imports by inlining their source code
  let src' = substImports src import_srcs

  -- putStrLn $ show (parseAndTycheck src')
  
  -- Parse and typecheck the final source code.
  -- On success, run the interpreter on the AST
  let results = case parseAndTycheck src' of
        Left s -> error s
        Right p' -> interpProg p'

  -- Get the last result and show it
  let result = results!!(length results - 1)
  case result of
    Left s -> putStrLn $ show s
    Right t -> putStrLn $ (if isNumericValue t
                            then show (int_of_nat t)
                            else show t)

  -- Show all results
  -- putStrLn $ show results

parseOnly f = parseProg "" f

parseGenOnly f = do
  p <- parseProg "" f
  let p' = genTypeVarsProg p
  return p'

parseAndTycheck f = do
  p <- parseProg "" f
  let p' = genTypeVarsProg p
  p'' <- runTycheck (tycheckProg p')
  return p''
