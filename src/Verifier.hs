module Verifier
  ( Term (..)
  , Formula (..)
  , Statement (..)
  , Spec (..)
  , Fact (..)
  , VerificationResult (..)
  , parseSpec
  , verificationConditions
  , verifyText
  , prove
  , proveText
  , parseFact
  , parseFacts
  , prettyTerm
  , prettyFormula
  , logicFacts
  , arithmeticFacts
  , defaultFacts
  , exampleSpecs
  , verifySpec
  ) where

import Data.Char (isSpace)
import Data.List (foldl')
import qualified Data.Map.Strict as Map
import qualified Data.Set as Set

-- Abstract syntax for expressions, assertions, and annotated WHILE commands.
data Term
  = Variable String
  | Integer Integer
  | Add Term Term
  | Subtract Term Term
  | Multiply Term Term
  | Divide Term Term
  | Maximum Term Term
  | Triangular Term
  deriving (Eq, Ord, Show)

data Formula
  = Truth
  | Falsity
  | Equal Term Term
  | Less Term Term
  | LessEqual Term Term
  | And Formula Formula
  | Not Formula
  | Implies Formula Formula
  | FormulaMeta String
  deriving (Eq, Ord, Show)

data Statement
  = Assign String Term
  | Assert Formula
  | Sequence [Statement]
  | Block [Statement]
  | While Formula Formula Statement
  | For String Term Term Formula Statement
  | If2 Formula Statement Statement
  deriving (Eq, Ord, Show)

data Spec = Spec Formula Statement Formula
  deriving (Eq, Ord, Show)

-- Rewriting and implication facts used by the generic proof engine.
data Fact
  = TermRewrite Term Term
  | TermEquation Term Term
  | FormulaRewrite Formula Formula
  | FormulaImplication Formula Formula
  deriving (Eq, Ord, Show)

data VerificationResult = VerificationResult
  { generatedConditions :: [Formula]
  , unprovedConditions :: [Formula]
  } deriving (Eq, Show)

-- A small S-expression tree keeps parsing independent of the verifier AST.
data SExpr = Atom String | List [SExpr]
  deriving (Eq, Show)

-- Parse a complete specification and reject malformed annotations or loops.
parseSpec :: String -> Either String Spec
parseSpec input = do
  sexpr <- parseSExpr input
  spec <- parseSpecExpr sexpr
  _ <- validateSpec spec
  pure spec

parseSExpr :: String -> Either String SExpr
parseSExpr input = do
  (expr, rest) <- parseExpr (dropWhile isSpace input)
  if all isSpace rest
    then Right expr
    else Left "Unexpected text after the specification."
  where
    parseExpr [] = Left "Unexpected end of input."
    parseExpr ('(' : rest) = parseList [] (dropWhile isSpace rest)
    parseExpr input' =
      let (token, rest) = span (\c -> not (isSpace c) && c /= '(' && c /= ')') input'
      in if null token then Left "Expected an atom." else Right (Atom token, rest)

    parseList _ [] = Left "Unclosed list."
    parseList items (')' : rest) = Right (List (reverse items), rest)
    parseList items input' = do
      (item, rest) <- parseExpr input'
      parseList (item : items) (dropWhile isSpace rest)

parseSpecExpr :: SExpr -> Either String Spec
parseSpecExpr (List [Atom "SPEC", pre, command, post]) =
  Spec <$> parseFormula pre <*> parseStatement command <*> parseFormula post
parseSpecExpr _ = Left "Expected (SPEC precondition command postcondition)."

parseStatement :: SExpr -> Either String Statement
parseStatement (List [Atom "ASSIGN", Atom variable, expression]) =
  Assign variable <$> parseTerm expression
parseStatement (List [Atom "ASSERT", formula]) = Assert <$> parseFormula formula
parseStatement (List (Atom "SEQ" : statements)) =
  Sequence <$> traverse parseStatement statements
parseStatement (List (Atom "BLOCK" : statements)) =
  Block <$> traverse parseStatement statements
parseStatement (List [Atom "WHILE", test, annotation, body]) =
  While <$> parseFormula test <*> parseAnnotation annotation <*> parseStatement body
parseStatement (List [Atom "FOR", Atom variable, lower, upper, annotation, body]) =
  For variable <$> parseTerm lower <*> parseTerm upper
    <*> parseAnnotation annotation <*> parseStatement body
parseStatement (List [Atom "IF2", test, yes, no]) =
  If2 <$> parseFormula test <*> parseStatement yes <*> parseStatement no
parseStatement _ = Left "Malformed WHILE statement."

parseAnnotation :: SExpr -> Either String Formula
parseAnnotation (List [Atom "ASSERT", formula]) = parseFormula formula
parseAnnotation _ = Left "Expected an ASSERT annotation."

parseTerm :: SExpr -> Either String Term
parseTerm (Atom token) =
  case reads token of
    [(number, "")] -> Right (Integer number)
    _ -> Right (Variable token)
parseTerm (List [Atom "max", left, right]) =
  Maximum <$> parseTerm left <*> parseTerm right
parseTerm (List [Atom "-", value]) =
  Subtract (Integer 0) <$> parseTerm value
parseTerm (List [left, Atom operator, right]) = do
  a <- parseTerm left
  b <- parseTerm right
  case operator of
    "+" -> Right (Add a b)
    "-" -> Right (Subtract a b)
    "*" -> Right (Multiply a b)
    "DIV" -> Right (Divide a b)
    "div" -> Right (Divide a b)
    _ -> Left ("Unknown arithmetic operator: " ++ operator)
parseTerm _ = Left "Malformed arithmetic expression."

parseFormula :: SExpr -> Either String Formula
parseFormula (Atom "T") = Right Truth
parseFormula (Atom "F") = Right Falsity
parseFormula (Atom "NIL") = Right Falsity
parseFormula (Atom name) = Right (FormulaMeta name)
parseFormula (List [left, Atom "=", right]) =
  Equal <$> parseTerm left <*> parseTerm right
parseFormula (List [left, Atom "<", right]) =
  Less <$> parseTerm left <*> parseTerm right
parseFormula (List [left, Atom "<=", right]) =
  LessEqual <$> parseTerm left <*> parseTerm right
parseFormula (List [left, Atom ">=", right]) =
  LessEqual <$> parseTerm right <*> parseTerm left
parseFormula (List [left, Atom ">", right]) =
  Less <$> parseTerm right <*> parseTerm left
parseFormula (List [Atom "and", left, right]) =
  And <$> parseFormula left <*> parseFormula right
parseFormula (List [left, Atom "and", right]) =
  And <$> parseFormula left <*> parseFormula right
parseFormula (List [Atom "not", formula]) = Not <$> parseFormula formula
parseFormula (List [Atom "implies", left, right]) =
  Implies <$> parseFormula left <*> parseFormula right
parseFormula (List [left, Atom "implies", right]) =
  Implies <$> parseFormula left <*> parseFormula right
parseFormula _ = Left "Malformed boolean expression."

-- Parse an equation and infer whether it rewrites terms or formulas.
parseFact :: String -> Either String Fact
parseFact source = do
  expression <- parseSExpr source
  case expression of
    List [Atom "TERM-REWRITE", left, right] ->
      TermRewrite <$> parseTerm left <*> parseTerm right
    List [Atom "TERM-EQUATION", left, right] ->
      TermEquation <$> parseTerm left <*> parseTerm right
    List [Atom "FORMULA-REWRITE", left, right] ->
      FormulaRewrite <$> parseFormula left <*> parseFormula right
    List [Atom "FORMULA-IMPLIES", antecedent, consequent] ->
      FormulaImplication <$> parseFormula antecedent <*> parseFormula consequent
    List [left, Atom "=", right]
      | isFormulaExpression left || isFormulaExpression right ->
          FormulaRewrite <$> parseFormula left <*> parseFormula right
      | otherwise ->
          TermRewrite <$> parseTerm left <*> parseTerm right
    _ -> Left "Expected a fact equation of the form ((left) = (right))."

parseFacts :: [String] -> Either String [Fact]
parseFacts = traverse parseFact

isFormulaExpression :: SExpr -> Bool
isFormulaExpression expression =
  case expression of
    Atom "T" -> True
    Atom "F" -> True
    Atom "NIL" -> True
    List [_, Atom operator, _] ->
      operator `elem` ["=", "<", "<=", ">", ">=", "and", "implies"]
    List (Atom operator : _) ->
      operator `elem` ["=", "<", "<=", ">", ">=", "and", "not", "implies"]
    _ -> False

-- Check sequence annotations and the side condition required by FOR.
validateSpec :: Spec -> Either String Spec
validateSpec spec@(Spec _ command _) = validateStatement command >> pure spec

validateStatement :: Statement -> Either String ()
validateStatement (Assign _ _) = Right ()
validateStatement (Assert _) = Left "ASSERT is only valid as a sequence annotation."
validateStatement (Sequence statements) = validateSequence statements
validateStatement (Block statements) = validateSequence statements
validateStatement (While _ _ body) = validateStatement body
validateStatement (For variable lower upper _ body) = do
  validateStatement body
  let forbidden = Set.insert variable (Set.union (termVariables lower) (termVariables upper))
  if Set.null (Set.intersection forbidden (assignedVariables body))
      && variable `Set.notMember` Set.union (termVariables lower) (termVariables upper)
    then Right ()
    else Left "FOR side condition violated: its index or bounds are modified by the body."
validateStatement (If2 _ yes no) =
  validateStatement yes >> validateStatement no

validateSequence :: [Statement] -> Either String ()
validateSequence [] = Left "A sequence or block must contain a statement."
validateSequence (Assert _ : rest) =
  case rest of
    [] -> Left "A trailing ASSERT has no command to annotate."
    Assert _ : _ -> Left "ASSERT annotations must be followed by a command."
    command : remaining -> validateStatement command >> validateSequenceTail remaining
validateSequence (Assign _ _ : rest) = validateSequenceTail rest
validateSequence (command : _) =
  validateStatement command >> Left "A non-assignment in a sequence needs an ASSERT annotation."

validateSequenceTail :: [Statement] -> Either String ()
validateSequenceTail [] = Right ()
validateSequenceTail (Assert _ : rest) =
  case rest of
    [] -> Left "A trailing ASSERT has no command to annotate."
    Assert _ : _ -> Left "ASSERT annotations must be followed by a command."
    command : remaining -> validateStatement command >> validateSequenceTail remaining
validateSequenceTail (Assign _ _ : rest) = validateSequenceTail rest
validateSequenceTail (command : _) =
  validateStatement command >> Left "A non-assignment in a sequence needs an ASSERT annotation."

assignedVariables :: Statement -> Set.Set String
assignedVariables (Assign variable _) = Set.singleton variable
assignedVariables (Assert _) = Set.empty
assignedVariables (Sequence statements) = Set.unions (map assignedVariables statements)
assignedVariables (Block statements) = Set.unions (map assignedVariables statements)
assignedVariables (While _ _ body) = assignedVariables body
assignedVariables (For variable _ _ _ body) =
  Set.insert variable (assignedVariables body)
assignedVariables (If2 _ yes no) =
  Set.union (assignedVariables yes) (assignedVariables no)

termVariables :: Term -> Set.Set String
termVariables (Variable name) = Set.singleton name
termVariables (Integer _) = Set.empty
termVariables (Add a b) = both a b
termVariables (Subtract a b) = both a b
termVariables (Multiply a b) = both a b
termVariables (Divide a b) = both a b
termVariables (Maximum a b) = both a b
termVariables (Triangular a) = termVariables a

both :: Term -> Term -> Set.Set String
both a b = Set.union (termVariables a) (termVariables b)

verificationConditions :: Spec -> Either String [Formula]
verificationConditions (Spec pre command post) = do
  validateStatement command
  generate pre command post

-- Generate the verification conditions for each command form.
generate :: Formula -> Statement -> Formula -> Either String [Formula]
generate pre (Assign variable expression) post =
  Right [Implies pre (substituteFormula variable expression post)]
generate _ (Assert _) _ =
  Left "ASSERT annotations are only interpreted within sequences."
generate pre (Sequence statements) post = generateSequence pre statements post
generate pre (Block statements) post = generateSequence pre statements post
generate pre (While test invariant body) post = do
  bodyConditions <- generate (And invariant test) body invariant
  pure
    ( [ Implies pre invariant
      , Implies (And invariant (Not test)) post
      ] ++ bodyConditions
    )
generate pre (For variable lower upper invariant body) post = do
  bodyConditions <-
    generate
      (And invariant (And (LessEqual lower (Variable variable))
                          (LessEqual (Variable variable) upper)))
      body
      (substituteFormula variable (Add (Variable variable) (Integer 1)) invariant)
  pure
    ( [ Implies pre (substituteFormula variable lower invariant)
      , Implies
          (substituteFormula variable (Add upper (Integer 1)) invariant)
          post
      , Implies (And pre (Less upper lower)) post
      ] ++ bodyConditions
    )
generate pre (If2 test yes no) post = do
  yesConditions <- generate (And pre test) yes post
  noConditions <- generate (And pre (Not test)) no post
  pure (yesConditions ++ noConditions)

generateSequence :: Formula -> [Statement] -> Formula -> Either String [Formula]
generateSequence pre statements post =
  case statements of
    Assert invariant : rest -> do
      -- Avoid a duplicate VC when the current precondition already contains it.
      let establishment =
            if syntacticallyEntails pre invariant then [] else [Implies pre invariant]
      restConditions <- generateSequence invariant rest post
      pure (establishment ++ restConditions)
    _ -> generateReversed pre (reverse statements) post

generateReversed :: Formula -> [Statement] -> Formula -> Either String [Formula]
generateReversed _ [] _ = Left "Cannot generate conditions for an empty sequence."
generateReversed pre [command] post = generate pre command post
generateReversed pre (Assign variable expression : rest) post =
  generateReversed pre rest (substituteFormula variable expression post)
generateReversed pre (command : Assert invariant : rest) post = do
  earlier <- generateReversed pre rest invariant
  later <- generate invariant command post
  pure (earlier ++ later)
generateReversed _ _ _ =
  Left "Malformed annotated sequence: a non-assignment needs a preceding ASSERT."

syntacticallyEntails :: Formula -> Formula -> Bool
syntacticallyEntails formula wanted
  | formula == wanted = True
syntacticallyEntails (And left right) wanted =
  syntacticallyEntails left wanted || syntacticallyEntails right wanted
syntacticallyEntails _ _ = False

substituteTerm :: String -> Term -> Term -> Term
substituteTerm variable replacement term =
  case term of
    Variable name | name == variable -> replacement
                  | otherwise -> term
    Integer _ -> term
    Add a b -> Add (recur a) (recur b)
    Subtract a b -> Subtract (recur a) (recur b)
    Multiply a b -> Multiply (recur a) (recur b)
    Divide a b -> Divide (recur a) (recur b)
    Maximum a b -> Maximum (recur a) (recur b)
    Triangular a -> Triangular (recur a)
  where
    recur = substituteTerm variable replacement

substituteFormula :: String -> Term -> Formula -> Formula
substituteFormula variable replacement formula =
  case formula of
    Truth -> Truth
    Falsity -> Falsity
    Equal a b -> Equal (substituteTerm variable replacement a)
                        (substituteTerm variable replacement b)
    Less a b -> Less (substituteTerm variable replacement a)
                      (substituteTerm variable replacement b)
    LessEqual a b -> LessEqual (substituteTerm variable replacement a)
                                (substituteTerm variable replacement b)
    And a b -> And (recur a) (recur b)
    Not a -> Not (recur a)
    Implies a b -> Implies (recur a) (recur b)
    FormulaMeta _ -> formula
  where
    recur = substituteFormula variable replacement

-- Facts are directed rewrite rules; variables in their patterns are metavariables.
logicFacts :: [Fact]
logicFacts =
  factsFromSource
    [ "((T implies X) = X)"
    , "((F implies X) = T)"
    , "((X implies T) = T)"
    , "((X implies X) = T)"
    , "((T and X) = X)"
    , "((X and T) = X)"
    , "((F and X) = F)"
    , "((X and F) = F)"
    , "((X = X) = T)"
    , "(((X and Y) implies Z) = (X implies (Y implies Z)))"
    ]

-- The arithmetic knowledge base is expressed as directed, reusable rewrite facts.
arithmeticFacts :: [Fact]
arithmeticFacts =
  factsFromSource
    [ "((X + 0) = X)"
    , "((0 + X) = X)"
    , "((X * 0) = 0)"
    , "((0 * X) = 0)"
    , "((X * 1) = X)"
    , "((1 * X) = X)"
    , "((not (X <= Y)) = (Y < X))"
    , "((not (X >= Y)) = (Y > X))"
    , "((not (X < Y)) = (X >= Y))"
    , "(((- X) >= (- Y)) = (X <= Y))"
    , "(((- X) >= Y) = (X <= (- Y)))"
    , "((- 0) = 0)"
    , "(((X < Y) implies (X <= Y)) = T)"
    , "((X - X) = 0)"
    , "(((X + Y) - Z) = (X + (Y - Z)))"
    , "(((X - Y) * Z) = ((X * Z) - (Y * Z)))"
    , "((X * (Y + Z)) = ((X * Y) + (X * Z)))"
    , "(((X + Y) * Z) = ((X * Z) + (Y * Z)))"
    , "(((X >= Y) implies ((X < Y) implies Z)) = T)"
    , "(((X <= Y) implies ((Y < X) implies Z)) = T)"
    , "((0 DIV X) = 0)"
    , "(((X DIV Y) + Z) = ((X + (Y * Z)) DIV Y))"
    , "(((X - Y) + Z) = (X + (Z - Y)))"
    , "((2 * X) = (X + X))"    
    , "((X + Y) = (Y + X))"
    , "((X * Y) = (Y * X))"
    ]

factsFromSource :: [String] -> [Fact]
factsFromSource sources =
  case parseFacts sources of
    Right facts -> facts
    Left problem -> error ("Invalid built-in proof fact: " ++ problem)

defaultFacts :: [Fact]
defaultFacts = logicFacts ++ arithmeticFacts

rewriteTerm :: [Fact] -> Term -> Term
rewriteTerm facts = rewrite 0 Set.empty
  where
    rewrite :: Int -> Set.Set Term -> Term -> Term
    rewrite fuel seen term
      | fuel >= 64 || term `Set.member` seen = term
      | otherwise =
          let nextSeen = Set.insert term seen
              descended = descend (rewrite (fuel + 1) Set.empty) term
          in case applyRule descended of
               Just result | result /= descended ->
                 rewrite (fuel + 1) nextSeen result
               _ -> descended

    descend recurse term =
      case term of
        Add a b -> Add (recurse a) (recurse b)
        Subtract a b -> Subtract (recurse a) (recurse b)
        Multiply a b -> Multiply (recurse a) (recurse b)
        Divide a b -> Divide (recurse a) (recurse b)
        Maximum a b -> Maximum (recurse a) (recurse b)
        Triangular a -> Triangular (recurse a)
        other -> other

    -- Keep reversible equations for equality proving, not normalization.
    applyRule term =
      firstJust
        [ Just result
        | fact <- facts
        , Just result <- [rewriteWithFact term fact]
        , not (rewritesBack result term)
        ]

    rewritesBack source target =
      any ((== Just target) . rewriteWithFact source) facts

    rewriteWithFact term (TermRewrite patternTerm replacement) = do
      bindings <- matchTerms emptyBindings patternTerm term
      pure (instantiateTerm bindings replacement)
    rewriteWithFact _ _ = Nothing

rewriteFormula :: [Fact] -> Formula -> Formula
rewriteFormula facts = rewrite 0
  where
    rewrite :: Int -> Formula -> Formula
    rewrite fuel formula
      | fuel >= 64 = formula
      | otherwise =
          let descended = descend (fuel + 1) formula
          in case applyRule descended of
               Just result | result /= descended -> rewrite (fuel + 1) result
               _ -> descended

    descend fuel formula =
      case formula of
        Equal a b -> Equal (rewriteTerm facts a) (rewriteTerm facts b)
        Less a b -> Less (rewriteTerm facts a) (rewriteTerm facts b)
        LessEqual a b -> LessEqual (rewriteTerm facts a) (rewriteTerm facts b)
        And a b -> And (rewrite fuel a) (rewrite fuel b)
        Not a -> Not (rewrite fuel a)
        Implies a b -> Implies (rewrite fuel a) (rewrite fuel b)
        FormulaMeta _ -> formula
        other -> other

    applyRule formula = firstJust (map (rewriteWithFact formula) facts)
    rewriteWithFact formula (FormulaRewrite patternFormula replacement) = do
      bindings <- matchFormula emptyBindings patternFormula formula
      pure (instantiateFormula bindings replacement)
    rewriteWithFact _ _ = Nothing

firstJust :: [Maybe a] -> Maybe a
firstJust [] = Nothing
firstJust (Just value : _) = Just value
firstJust (Nothing : rest) = firstJust rest

verifyText :: [Fact] -> String -> Either String VerificationResult
verifyText facts source = parseSpec source >>= verifySpec facts

-- Prove one formula using the built-in Chapter 10/11 facts.
prove :: Formula -> Bool
prove = proveFormula defaultFacts []

-- Parse and prove a single formula without requiring a WHILE specification.
proveText :: String -> Either String Bool
proveText source = do
  expression <- parseSExpr source
  formula <- parseFormula expression
  pure (prove formula)

-- Generate VCs, then keep the ones the bounded prover cannot discharge.
verifySpec :: [Fact] -> Spec -> Either String VerificationResult
verifySpec facts spec = do
  conditions <- verificationConditions spec
  let allFacts = defaultFacts ++ facts
      failures = filter (not . proveFormula allFacts []) conditions
  pure (VerificationResult conditions failures)

proveFormula :: [Fact] -> [Formula] -> Formula -> Bool
proveFormula facts assumptions goal =
  let normalizedAssumptions =
        concatMap (flattenAnd . rewriteFormula facts) assumptions
      substitutions = equalitySubstitutions normalizedAssumptions
      normalizedGoal =
        rewriteFormula facts (substituteAllFormula substitutions goal)
  in contradictoryByFacts facts normalizedAssumptions
      || normalizedGoal == Truth
      || normalizedGoal `elem` normalizedAssumptions
      || proveByShape facts normalizedAssumptions normalizedGoal

proveByShape :: [Fact] -> [Formula] -> Formula -> Bool
proveByShape facts assumptions goal =
  case goal of
    Truth -> True
    Falsity -> applyFacts facts assumptions goal
    And left right ->
      proveFormula facts assumptions left && proveFormula facts assumptions right
    Implies antecedent consequent ->
      proveFormula facts (antecedent : assumptions) consequent
    Not proposition ->
      proveFormula facts (proposition : assumptions) Falsity
    Equal left right ->
      left == right
        || rewriteTerm facts left == rewriteTerm facts right
        || termRewriteProves facts left right
        || termEquationProves facts left right
        || applyFacts facts assumptions goal
    Less left right ->
      knownComparison assumptions (Less left right) || applyFacts facts assumptions goal
    LessEqual left right ->
      knownComparison assumptions (LessEqual left right) || applyFacts facts assumptions goal
    FormulaMeta _ -> False

applyFacts :: [Fact] -> [Formula] -> Formula -> Bool
applyFacts facts assumptions goal =
  any proveWithFact facts
  where
    proveWithFact (FormulaImplication patternAntecedent patternConsequent) =
      case matchFormula emptyBindings patternConsequent goal of
        Nothing -> False
        Just bindings ->
          let antecedent = instantiateFormula bindings patternAntecedent
          in proveFormula facts assumptions antecedent
    proveWithFact _ = False

termEquationProves :: [Fact] -> Term -> Term -> Bool
termEquationProves facts left right = any matches facts
  where
    matches (TermEquation patternLeft patternRight) =
      matchesDirection patternLeft patternRight
        || matchesDirection patternRight patternLeft
    matches _ = False

    matchesDirection patternLeft patternRight =
      case matchTerms emptyBindings patternLeft left of
        Nothing -> False
        Just bindings -> instantiateTerm bindings patternRight == right

termRewriteProves :: [Fact] -> Term -> Term -> Bool
termRewriteProves facts left right = any matches facts
  where
    matches (TermRewrite patternLeft patternRight) =
      matchesDirection patternLeft patternRight
        || matchesDirection patternRight patternLeft
    matches _ = False

    matchesDirection patternLeft patternRight =
      case matchTerms emptyBindings patternLeft left of
        Nothing -> False
        Just bindings -> instantiateTerm bindings patternRight == right

data MatchBindings = MatchBindings
  { termBindings :: Map.Map String Term
  , formulaBindings :: Map.Map String Formula
  }

emptyBindings :: MatchBindings
emptyBindings = MatchBindings Map.empty Map.empty

matchFormula :: MatchBindings -> Formula -> Formula -> Maybe MatchBindings
matchFormula bindings patternFormula valueFormula =
  case (patternFormula, valueFormula) of
    (FormulaMeta name, value) ->
      case Map.lookup name (formulaBindings bindings) of
        Nothing ->
          Just bindings
            { formulaBindings = Map.insert name value (formulaBindings bindings) }
        Just existing | existing == value -> Just bindings
                      | otherwise -> Nothing
    (Truth, Truth) -> Just bindings
    (Falsity, Falsity) -> Just bindings
    (Equal a b, Equal x y) -> matchTerms bindings a x >>= \next -> matchTerms next b y
    (Less a b, Less x y) -> matchTerms bindings a x >>= \next -> matchTerms next b y
    (LessEqual a b, LessEqual x y) ->
      matchTerms bindings a x >>= \next -> matchTerms next b y
    (And a b, And x y) -> matchFormula bindings a x >>= \next -> matchFormula next b y
    (Not a, Not x) -> matchFormula bindings a x
    (Implies a b, Implies x y) ->
      matchFormula bindings a x >>= \next -> matchFormula next b y
    _ -> Nothing

matchTerms :: MatchBindings -> Term -> Term -> Maybe MatchBindings
matchTerms bindings patternTerm valueTerm =
  case patternTerm of
    Variable name ->
      case Map.lookup name (termBindings bindings) of
        Nothing ->
          Just bindings
            { termBindings = Map.insert name valueTerm (termBindings bindings) }
        Just existing | existing == valueTerm -> Just bindings
                      | otherwise -> Nothing
    Integer number ->
      if valueTerm == Integer number then Just bindings else Nothing
    Add a b -> matchBinary bindings Add a b valueTerm
    Subtract a b -> matchBinary bindings Subtract a b valueTerm
    Multiply a b -> matchBinary bindings Multiply a b valueTerm
    Divide a b -> matchBinary bindings Divide a b valueTerm
    Maximum a b -> matchBinary bindings Maximum a b valueTerm
    Triangular a ->
      case valueTerm of
        Triangular x -> matchTerms bindings a x
        _ -> Nothing

instantiateTerm :: MatchBindings -> Term -> Term
instantiateTerm bindings = go
  where
    go term =
      case term of
        Variable name -> Map.findWithDefault term name (termBindings bindings)
        Integer _ -> term
        Add a b -> Add (go a) (go b)
        Subtract a b -> Subtract (go a) (go b)
        Multiply a b -> Multiply (go a) (go b)
        Divide a b -> Divide (go a) (go b)
        Maximum a b -> Maximum (go a) (go b)
        Triangular a -> Triangular (go a)

matchBinary
  :: MatchBindings
  -> (Term -> Term -> Term)
  -> Term
  -> Term
  -> Term
  -> Maybe MatchBindings
matchBinary bindings constructor a b valueTerm
  | termConstructorMatches constructor valueTerm =
      let (x, y) = termChildren valueTerm
      in matchTerms bindings a x >>= \next -> matchTerms next b y
  | otherwise = Nothing

termConstructorMatches :: (Term -> Term -> Term) -> Term -> Bool
termConstructorMatches constructor term =
  case term of
    Add _ _ -> sameConstructor constructor Add
    Subtract _ _ -> sameConstructor constructor Subtract
    Multiply _ _ -> sameConstructor constructor Multiply
    Divide _ _ -> sameConstructor constructor Divide
    Maximum _ _ -> sameConstructor constructor Maximum
    _ -> False
  where
    sameConstructor left right =
      case (left (Integer 0) (Integer 0), right (Integer 0) (Integer 0)) of
        (Add _ _, Add _ _) -> True
        (Subtract _ _, Subtract _ _) -> True
        (Multiply _ _, Multiply _ _) -> True
        (Divide _ _, Divide _ _) -> True
        (Maximum _ _, Maximum _ _) -> True
        _ -> False

termChildren :: Term -> (Term, Term)
termChildren (Add a b) = (a, b)
termChildren (Subtract a b) = (a, b)
termChildren (Multiply a b) = (a, b)
termChildren (Divide a b) = (a, b)
termChildren (Maximum a b) = (a, b)
termChildren _ = (Integer 0, Integer 0)

instantiateFormula :: MatchBindings -> Formula -> Formula
instantiateFormula bindings = go
  where
    go formula =
      case formula of
        FormulaMeta name ->
          maybe formula go (Map.lookup name (formulaBindings bindings))
        Truth -> Truth
        Falsity -> Falsity
        Equal a b -> Equal (instantiateTerm bindings a) (instantiateTerm bindings b)
        Less a b -> Less (instantiateTerm bindings a) (instantiateTerm bindings b)
        LessEqual a b ->
          LessEqual (instantiateTerm bindings a) (instantiateTerm bindings b)
        And a b -> And (go a) (go b)
        Not proposition -> Not (go proposition)
        Implies antecedent consequent -> Implies (go antecedent) (go consequent)

flattenAnd :: Formula -> [Formula]
flattenAnd (And left right) = flattenAnd left ++ flattenAnd right
flattenAnd Truth = []
flattenAnd formula = [formula]

equalitySubstitutions :: [Formula] -> Map.Map String Term
equalitySubstitutions = foldl' add Map.empty
  where
    add substitutions (Equal (Variable name) term)
      | name `Set.notMember` termVariables term = Map.insert name term substitutions
    add substitutions (Equal term (Variable name))
      | name `Set.notMember` termVariables term = Map.insert name term substitutions
    add substitutions _ = substitutions

substituteAllFormula :: Map.Map String Term -> Formula -> Formula
substituteAllFormula substitutions = goFormula Set.empty
  where
    goFormula seen formula =
      case formula of
        Truth -> Truth
        Falsity -> Falsity
        Equal a b -> Equal (goTerm seen a) (goTerm seen b)
        Less a b -> Less (goTerm seen a) (goTerm seen b)
        LessEqual a b -> LessEqual (goTerm seen a) (goTerm seen b)
        And a b -> And (goFormula seen a) (goFormula seen b)
        Not a -> Not (goFormula seen a)
        Implies a b -> Implies (goFormula seen a) (goFormula seen b)
        FormulaMeta _ -> formula
    goTerm seen term =
      case term of
        Variable name
          | name `Set.member` seen -> term
          | otherwise ->
              case Map.lookup name substitutions of
                Just replacement -> goTerm (Set.insert name seen) replacement
                Nothing -> term
        Integer _ -> term
        Add a b -> Add (goTerm seen a) (goTerm seen b)
        Subtract a b -> Subtract (goTerm seen a) (goTerm seen b)
        Multiply a b -> Multiply (goTerm seen a) (goTerm seen b)
        Divide a b -> Divide (goTerm seen a) (goTerm seen b)
        Maximum a b -> Maximum (goTerm seen a) (goTerm seen b)
        Triangular a -> Triangular (goTerm seen a)

knownComparison :: [Formula] -> Formula -> Bool
knownComparison assumptions wanted = wanted `elem` assumptions

contradictoryByFacts :: [Fact] -> [Formula] -> Bool
contradictoryByFacts facts assumptions = any detects facts
  where
    detects (FormulaImplication antecedent Falsity) =
      case matchPremises emptyBindings (flattenAnd antecedent) assumptions of
        Just _ -> True
        Nothing -> False
    detects _ = False

    matchPremises bindings [] _ = Just bindings
    matchPremises bindings (premise : premises) available =
      firstJust
        [ matchFormula bindings premise actual
            >>= \next -> matchPremises next premises available
        | actual <- available
        ]

prettyTerm :: Term -> String
prettyTerm term =
  case term of
    Variable name -> name
    Integer number -> show number
    Add a b -> binary "+" a b
    Subtract a b -> binary "-" a b
    Multiply a b -> binary "*" a b
    Divide a b -> binary "DIV" a b
    Maximum a b -> "(max " ++ prettyTerm a ++ " " ++ prettyTerm b ++ ")"
    Triangular a -> "(tri " ++ prettyTerm a ++ ")"
  where
    binary operator a b =
      "(" ++ prettyTerm a ++ " " ++ operator ++ " " ++ prettyTerm b ++ ")"

prettyFormula :: Formula -> String
prettyFormula formula =
  case formula of
    Truth -> "T"
    Falsity -> "NIL"
    Equal a b -> relation "=" a b
    Less a b -> relation "<" a b
    LessEqual a b -> relation "<=" a b
    And a b -> "(" ++ prettyFormula a ++ " and " ++ prettyFormula b ++ ")"
    Not a -> "(not " ++ prettyFormula a ++ ")"
    Implies a b -> "(" ++ prettyFormula a ++ " implies " ++ prettyFormula b ++ ")"
    FormulaMeta name -> name
  where
    relation operator a b =
      "(" ++ prettyTerm a ++ " " ++ operator ++ " " ++ prettyTerm b ++ ")"

-- Book examples paired with optional facts used by the theorem prover.
exampleSpecs :: [(String, String, [Fact])]
exampleSpecs =
  [ ( "swap without temporary (expected failure)"
    , unlines
        [ "(SPEC"
        , "  ((X = x) and (Y = y))"
        , "  (SEQ"
        , "    (ASSIGN X Y)"
        , "    (ASSIGN Y X))"
        , "  ((X = y) and (Y = x)))"
        ]
    , []
    )
  , ( "swap with temporary"
    , unlines
        [ "(SPEC"
        , "  ((X = x) and (Y = y))"
        , "  (SEQ"
        , "    (ASSIGN R X)"
        , "    (ASSIGN X Y)"
        , "    (ASSIGN Y R))"
        , "  ((X = y) and (Y = x)))"
        ]
    , []
    )
  , ( "integer division"
    , unlines
        [ "(SPEC"
        , "  T"
        , "  (BLOCK"
        , "    (ASSIGN R X)"
        , "    (ASSIGN Q 0)"
        , "    (ASSERT ((R = X) and (Q = 0)))"
        , "    (WHILE"
        , "      (Y <= R)"
        , "      (ASSERT (X = (R + (Y * Q))))"
        , "      (BLOCK"
        , "        (ASSIGN R (R - Y))"
        , "        (ASSIGN Q (Q + 1)))))"
        , "  ((R < Y) and (X = (R + (Y * Q)))))"
        ]
    , []
    )
  , ( "sum with no lower-bound precondition (expected failure)"
    , unlines
        [ "(SPEC"
        , "  T"
        , "  (SEQ"
        , "    (ASSIGN X 0)"
        , "    (ASSERT (X = 0))"
        , "    (FOR N 1 M"
        , "      (ASSERT (X = (((N - 1) * N) DIV 2)))"
        , "      (ASSIGN X (X + N))))"
        , "  (X = ((M * (M + 1)) DIV 2)))"
        ]
    , []
    )
  , ( "sum with only a precondition (expected failure)"
    , unlines
        [ "(SPEC"
        , "  (M >= 1)"
        , "  (SEQ"
        , "    (ASSIGN X 0)"
        , "    (ASSERT (X = 0))"
        , "    (FOR N 1 M"
        , "      (ASSERT (X = (((N - 1) * N) DIV 2)))"
        , "      (ASSIGN X (X + N))))"
        , "  (X = ((M * (M + 1)) DIV 2)))"
        ]
    , []
    )
  , ( "sum with strengthened annotation"
    , unlines
        [ "(SPEC"
        , "  (M >= 1)"
        , "  (SEQ"
        , "    (ASSIGN X 0)"
        , "    (ASSERT ((X = 0) and (M >= 1)))"
        , "    (FOR N 1 M"
        , "      (ASSERT (X = (((N - 1) * N) DIV 2)))"
        , "      (ASSIGN X (X + N))))"
        , "  (X = ((M * (M + 1)) DIV 2)))"
        ]
    , []
    )
  , ( "maximum without facts (expected failure)"
    , unlines
        [ "(SPEC"
        , "  T"
        , "  (IF2"
        , "    (X >= Y)"
        , "    (ASSIGN MAX X)"
        , "    (ASSIGN MAX Y))"
        , "  (MAX = (max X Y)))"
        ]
    , []
    )
  , ( "maximum with supplied facts"
    , unlines
        [ "(SPEC"
        , "  T"
        , "  (IF2"
        , "    (X >= Y)"
        , "    (ASSIGN MAX X)"
        , "    (ASSIGN MAX Y))"
        , "  (MAX = (max X Y)))"
        ]
    , [ FormulaImplication
          (LessEqual (Variable "Y") (Variable "X"))
          (Equal (Variable "X") (Maximum (Variable "X") (Variable "Y")))
      , FormulaImplication
          (Less (Variable "X") (Variable "Y"))
          (Equal (Variable "Y") (Maximum (Variable "X") (Variable "Y")))
      ]
    )
  ]
