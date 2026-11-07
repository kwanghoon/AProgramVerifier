module Main (main) where

import Data.Char (toLower)
import System.IO (hFlush, isEOF, stdout)
import Text.Read (readMaybe)
import Verifier

main :: IO ()
main = do
  putStrLn "A Simple Program Verifier - Chapter 11 examples"
  menuLoop

menuLoop :: IO ()
menuLoop = do
  putStrLn "\nExamples:"
  mapM_ printMenuItem (zip [1 :: Int ..] exampleSpecs)
  putStrLn "  9. Prove a proposition (Chapter 10)"
  putStrLn "  0. Exit"
  putStr "Choose an example number: "
  hFlush stdout
  atEnd <- isEOF
  if atEnd
    then putStrLn "\nGoodbye."
    else do
      choice <- getLine
      case map toLower choice of
        "q" -> putStrLn "Goodbye."
        "0" -> putStrLn "Goodbye."
        "9" -> do
          proveLoop
          menuLoop
        _ ->
          case readMaybe choice of
            Just number
              | number >= 1 && number <= length exampleSpecs -> do
                  runExample (exampleSpecs !! (number - 1))
                  menuLoop
            _ -> do
              putStrLn "Please enter one of the listed numbers, 0, or q."
              menuLoop

proveLoop :: IO ()
proveLoop = do
  putStrLn "\nChapter 10 theorem prover (default facts are included)."
  putStrLn "Enter a formula in Lisp-style syntax, or type 'back' to return."
  proofPrompt
  where
    proofPrompt = do
      putStr "\nFormula> "
      hFlush stdout
      atEnd <- isEOF
      if atEnd
        then putStrLn "\nReturning to the main menu."
        else do
          source <- getLine
          if map toLower source == "back"
            then pure ()
            else do
              case proveText source of
                Left problem -> putStrLn ("Input error: " ++ problem)
                Right True -> putStrLn "Proved."
                Right False -> putStrLn "Could not prove this formula."
              proofPrompt

printMenuItem :: (Int, (String, String, [Fact])) -> IO ()
printMenuItem (number, (name, _, _)) =
  putStrLn ("  " ++ show number ++ ". " ++ name)

runExample :: (String, String, [Fact]) -> IO ()
runExample (name, source, facts) = do
  putStrLn ("\n== " ++ name ++ " ==")
  putStrLn "Annotated WHILE specification:"
  putStrLn ("  " ++ source)
  case verifyText facts source of
    Left problem -> putStrLn ("Error: " ++ problem)
    Right result -> do
      putStrLn "Verification conditions:"
      mapM_ (putStrLn . ("  " ++) . prettyFormula) (generatedConditions result)
      if null (unprovedConditions result)
        then putStrLn "Result: all conditions proved."
        else do
          putStrLn "Result: some conditions could not be proved:"
          mapM_ (putStrLn . ("  " ++) . prettyFormula) (unprovedConditions result)
