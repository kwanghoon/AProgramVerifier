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
  checkProverInterface
  checkFactParser
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

checkProverInterface :: IO ()
checkProverInterface = do
  let results =
        [ proveText "(1 = 1)"
        , proveText "(X = Y)"
        , proveText "((0 + X) = X)"
        , proveText "((X < Y) implies (X <= Y))"
        , proveText "((X + 1) = (1 + X))"
        , proveText "((X * Y) = (Y * X))"
        , proveText "(not-an-operator X Y)"
        ]
  unless
    (results ==
      [ Right True
      , Right False
      , Right True
      , Right True
      , Right True
      , Right True
      , Left "Malformed boolean expression."
      ]) $ do
    putStrLn ("Unexpected standalone prover results: " ++ show results)
    exitFailure

checkFactParser :: IO ()
checkFactParser = do
  let facts =
        [ "((x + 0) = x)"
        , "((x + 1) = (1 + x))"
        , "((T and X) = X)"
        , "(((x < y) implies (x <= y)) = T)"
        ]
  unless ((length <$> parseFacts facts) == Right 4) $ do
    putStrLn "String fact declarations did not parse."
    exitFailure
  unless (length logicFacts == 10 && length arithmeticFacts == 26) $ do
    putStrLn "Built-in fact strings did not parse into the expected fact lists."
    exitFailure
  case
      ( parseFact "((x + 0) = x)"
      , parseFact "((T and X) = X)"
      , parseFact "((X + Y) = (Y + X))"
      ) of
    ( Right (TermRewrite _ _)
      , Right (FormulaRewrite _ _)
      , Right (TermRewrite _ _)
      ) -> pure ()
    _ -> do
      putStrLn "Untagged equations were not classified as term/formula facts."
      exitFailure
