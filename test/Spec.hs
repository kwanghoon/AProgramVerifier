module Main (main) where

import Control.Monad (unless)
import System.Exit (exitFailure)
import Verifier

main :: IO ()
main = do
  let expectations =
        [ False
        , True
        , True
        , False
        , False
        , True
        , False
        , True
        ]
      outcomes =
        [ either (const False) (null . unprovedConditions) (verifyText facts source)
        | (_, source, facts) <- exampleSpecs
        ]
  unless (outcomes == expectations) $ do
    putStrLn ("Unexpected example results: " ++ show outcomes)
    exitFailure
  checkConditionCounts
  checkMalformedInput
  putStrLn "All verifier tests passed."

checkConditionCounts :: IO ()
checkConditionCounts = do
  let counts =
        [ length (generatedConditions result)
        | (_, source, facts) <- exampleSpecs
        , Right result <- [verifyText facts source]
        ]
  unless (counts == [1, 1, 4, 5, 5, 5, 2, 2]) $ do
    putStrLn ("Unexpected VC counts: " ++ show counts)
    exitFailure

checkMalformedInput :: IO ()
checkMalformedInput =
  case parseSpec "(SPEC T (SEQ (ASSIGN X 0) (WHILE T (ASSERT T) (ASSIGN X 1))) T)" of
    Left _ -> pure ()
    Right _ -> do
      putStrLn "Malformed unannotated sequence was accepted."
      exitFailure
