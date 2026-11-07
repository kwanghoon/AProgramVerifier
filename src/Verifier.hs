module Verifier
  ( Term (..)
  , Formula (..)
  , Statement (..)
  , Spec (..)
  , VerificationResult (..)
  , parseSpec
  , verificationConditions
  , verifyText
  , prettyTerm
  , prettyFormula
  , exampleSpecs
  , verifySpec
  ) where

import Data.Char (isSpace)
import Data.List (foldl', sort)
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
parseFormula (Atom "NIL") = Right Falsity
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
parseFormula _ = Left "Malformed boolean expression."

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
  where
    recur = substituteFormula variable replacement

type Polynomial = Map.Map [Term] Rational

-- Normalize arithmetic expressions into polynomials when possible.
polynomial :: Term -> Polynomial
polynomial term =
  case simplifyTerm term of
    Integer n -> constant (fromInteger n)
    asVariable@(Variable _) -> monomial asVariable
    Add a b ->
      case triangularSum a b of
        Just result -> atomPolynomial result
        Nothing -> addPolynomials (polynomial a) (polynomial b)
    Subtract a b -> addPolynomials (polynomial a) (scalePolynomial (-1) (polynomial b))
    Multiply a b -> multiplyPolynomials (polynomial a) (polynomial b)
    Divide numerator divisor ->
      case (simplifyTerm numerator, simplifyTerm divisor) of
        (Integer a, Integer b) | b /= 0 -> constant (fromInteger (a `div` b))
        (productTerm, Integer 2) ->
          case consecutiveProduct productTerm of
            Just value -> atomPolynomial (Triangular value)
            Nothing -> atomPolynomial (Divide productTerm (Integer 2))
        (a, b) -> atomPolynomial (Divide a b)
    Maximum a b -> atomPolynomial (Maximum (canonicalTerm a) (canonicalTerm b))
    Triangular a -> atomPolynomial (Triangular (canonicalTerm a))

canonicalTerm :: Term -> Term
canonicalTerm term =
  case simplifyTerm term of
    Add a b -> Add (canonicalTerm a) (canonicalTerm b)
    Subtract a b -> Subtract (canonicalTerm a) (canonicalTerm b)
    Multiply a b -> Multiply (canonicalTerm a) (canonicalTerm b)
    Divide a b -> Divide (canonicalTerm a) (canonicalTerm b)
    Maximum a b -> Maximum (canonicalTerm a) (canonicalTerm b)
    Triangular a -> Triangular (canonicalTerm a)
    other -> other

simplifyTerm :: Term -> Term
simplifyTerm term =
  case term of
    Add left right ->
      simplifyAdd (simplifyTerm left) (simplifyTerm right)
    Subtract left right ->
      simplifySubtract (simplifyTerm left) (simplifyTerm right)
    Multiply left right ->
      simplifyMultiply (simplifyTerm left) (simplifyTerm right)
    Divide left right ->
      Divide (simplifyTerm left) (simplifyTerm right)
    Maximum left right ->
      Maximum (simplifyTerm left) (simplifyTerm right)
    Triangular value -> Triangular (simplifyTerm value)
    other -> other

simplifyAdd :: Term -> Term -> Term
simplifyAdd (Integer a) (Integer b) = Integer (a + b)
simplifyAdd (Integer 0) b = b
simplifyAdd a (Integer 0) = a
simplifyAdd (Subtract a (Integer n)) (Integer m) | n == m = a
simplifyAdd (Integer n) (Subtract a (Integer m)) | n == m = a
simplifyAdd (Triangular a) b | sameTerm a b = Triangular (simplifyAdd a (Integer 1))
simplifyAdd a (Triangular b) | sameTerm a b = Triangular (simplifyAdd b (Integer 1))
simplifyAdd a b = Add a b

simplifySubtract :: Term -> Term -> Term
simplifySubtract (Integer a) (Integer b) = Integer (a - b)
simplifySubtract a (Integer 0) = a
simplifySubtract a b | sameTerm a b = Integer 0
simplifySubtract (Add a (Integer n)) (Integer m) | n == m = a
simplifySubtract (Add (Integer n) a) (Integer m) | n == m = a
simplifySubtract a b = Subtract a b

simplifyMultiply :: Term -> Term -> Term
simplifyMultiply (Integer a) (Integer b) = Integer (a * b)
simplifyMultiply (Integer 0) _ = Integer 0
simplifyMultiply _ (Integer 0) = Integer 0
simplifyMultiply (Integer 1) b = b
simplifyMultiply a (Integer 1) = a
simplifyMultiply a b = Multiply a b

sameTerm :: Term -> Term -> Bool
sameTerm a b = canonicalTerm a == canonicalTerm b

triangularSum :: Term -> Term -> Maybe Term
triangularSum left right =
  case (asTriangular left, asTriangular right) of
    (Just a, _) | sameTerm a right -> Just (Triangular (simplifyAdd a (Integer 1)))
    (_, Just b) | sameTerm left b -> Just (Triangular (simplifyAdd b (Integer 1)))
    _ -> Nothing

asTriangular :: Term -> Maybe Term
asTriangular term =
  case simplifyTerm term of
    Triangular value -> Just value
    Divide numerator (Integer 2) ->
      consecutiveProduct numerator
    _ -> Nothing

consecutiveProduct :: Term -> Maybe Term
consecutiveProduct (Multiply a b)
  | isPrevious a b = Just (canonicalTerm b)
  | isPrevious b a = Just (canonicalTerm a)
consecutiveProduct _ = Nothing

isPrevious :: Term -> Term -> Bool
isPrevious candidate successor =
  sameTerm candidate (simplifySubtract successor (Integer 1))

atomPolynomial :: Term -> Polynomial
atomPolynomial term = monomial (canonicalTerm term)

constant :: Rational -> Polynomial
constant 0 = Map.empty
constant number = Map.singleton [] number

monomial :: Term -> Polynomial
monomial term = Map.singleton [term] 1

addPolynomials :: Polynomial -> Polynomial -> Polynomial
addPolynomials a b = Map.filter (/= 0) (Map.unionWith (+) a b)

scalePolynomial :: Rational -> Polynomial -> Polynomial
scalePolynomial factor = Map.filter (/= 0) . Map.map (factor *)

multiplyPolynomials :: Polynomial -> Polynomial -> Polynomial
multiplyPolynomials a b =
  Map.filter (/= 0) $
    Map.fromListWith (+)
      [ (sort (left ++ right), x * y)
      | (left, x) <- Map.toList a
      , (right, y) <- Map.toList b
      ]

verifyText :: [Formula] -> String -> Either String VerificationResult
verifyText facts source = parseSpec source >>= verifySpec facts

-- Generate VCs, then keep the ones the bounded prover cannot discharge.
verifySpec :: [Formula] -> Spec -> Either String VerificationResult
verifySpec facts spec = do
  conditions <- verificationConditions spec
  let failures = filter (not . proveFormula facts []) conditions
  pure (VerificationResult conditions failures)

proveFormula :: [Formula] -> [Formula] -> Formula -> Bool
proveFormula facts assumptions goal =
  let normalizedAssumptions = map normalizeFormula (concatMap flattenAnd assumptions)
      substitutions = equalitySubstitutions normalizedAssumptions
      normalizedGoal = normalizeFormula (substituteAllFormula substitutions goal)
  in inconsistent normalizedAssumptions
      || normalizedGoal == Truth
      || normalizedGoal `elem` normalizedAssumptions
      || proveByShape facts normalizedAssumptions normalizedGoal

proveByShape :: [Formula] -> [Formula] -> Formula -> Bool
proveByShape facts assumptions goal =
  case goal of
    Truth -> True
    Falsity -> False
    And left right ->
      proveFormula facts assumptions left && proveFormula facts assumptions right
    Implies antecedent consequent ->
      proveFormula facts (antecedent : assumptions) consequent
    Not proposition ->
      inconsistent (normalizeFormula proposition : assumptions)
    Equal left right ->
      polynomial left == polynomial right || applyFacts facts assumptions goal
    Less left right ->
      knownComparison assumptions (Less left right)
        || maybe False (uncurry (<)) (constantPair left right)
        || applyFacts facts assumptions goal
    LessEqual left right ->
      knownComparison assumptions (LessEqual left right)
        || maybe False (uncurry (<=)) (constantPair left right)
        || applyFacts facts assumptions goal

applyFacts :: [Formula] -> [Formula] -> Formula -> Bool
applyFacts facts assumptions goal =
  any proveWithFact facts
  where
    proveWithFact (Implies patternAntecedent patternConsequent) =
      case matchFormula Map.empty patternConsequent goal of
        Nothing -> False
        Just bindings ->
          let antecedent = instantiateFormula bindings patternAntecedent
          in proveFormula [] assumptions antecedent
    proveWithFact _ = False

matchFormula :: Map.Map String Term -> Formula -> Formula -> Maybe (Map.Map String Term)
matchFormula bindings patternFormula valueFormula =
  case (patternFormula, valueFormula) of
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

matchTerms :: Map.Map String Term -> Term -> Term -> Maybe (Map.Map String Term)
matchTerms bindings patternTerm valueTerm =
  case patternTerm of
    Variable name ->
      case Map.lookup name bindings of
        Nothing -> Just (Map.insert name valueTerm bindings)
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

matchBinary
  :: Map.Map String Term
  -> (Term -> Term -> Term)
  -> Term
  -> Term
  -> Term
  -> Maybe (Map.Map String Term)
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

instantiateFormula :: Map.Map String Term -> Formula -> Formula
instantiateFormula bindings formula =
  foldl'
    (\current (name, value) -> substituteFormula name value current)
    formula
    (Map.toList bindings)

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

normalizeFormula :: Formula -> Formula
normalizeFormula formula =
  case formula of
    Truth -> Truth
    Falsity -> Falsity
    Equal a b
      | polynomial a == polynomial b -> Truth
      | otherwise -> Equal (canonicalTerm a) (canonicalTerm b)
    Less a b ->
      let left = canonicalTerm a
          right = canonicalTerm b
      in case constantPair left right of
           Just (x, y) -> if x < y then Truth else Falsity
           Nothing -> Less left right
    LessEqual a b ->
      let left = canonicalTerm a
          right = canonicalTerm b
      in case constantPair left right of
           Just (x, y) -> if x <= y then Truth else Falsity
           Nothing -> LessEqual left right
    And a b -> simplifyAnd (normalizeFormula a) (normalizeFormula b)
    Not proposition ->
      case normalizeFormula proposition of
        Truth -> Falsity
        Falsity -> Truth
        Less a b -> LessEqual b a
        LessEqual a b -> Less b a
        Not inner -> inner
        other -> Not other
    Implies antecedent consequent ->
      case (normalizeFormula antecedent, normalizeFormula consequent) of
        (Falsity, _) -> Truth
        (_, Truth) -> Truth
        (Truth, other) -> other
        (other, Falsity) -> normalizeFormula (Not other)
        (left, right) -> Implies left right

simplifyAnd :: Formula -> Formula -> Formula
simplifyAnd Truth right = right
simplifyAnd left Truth = left
simplifyAnd Falsity _ = Falsity
simplifyAnd _ Falsity = Falsity
simplifyAnd left right | left == right = left
simplifyAnd left right = And left right

constantPair :: Term -> Term -> Maybe (Rational, Rational)
constantPair a b = (,) <$> constantValue a <*> constantValue b

constantValue :: Term -> Maybe Rational
constantValue term =
  case Map.toList (polynomial term) of
    [] -> Just 0
    [([], value)] -> Just value
    _ -> Nothing

knownComparison :: [Formula] -> Formula -> Bool
knownComparison assumptions wanted =
  wanted `elem` assumptions
    || case wanted of
         Less a b ->
           LessEqual b a `elem` assumptions
             || Less a b `elem` assumptions
         LessEqual a b ->
           Less b a `elem` assumptions
             || LessEqual a b `elem` assumptions
         _ -> False

inconsistent :: [Formula] -> Bool
inconsistent assumptions =
  Falsity `elem` assumptions || any hasComplement assumptions
  where
    hasComplement (Less a b) = LessEqual b a `elem` assumptions
    hasComplement (LessEqual a b) = Less b a `elem` assumptions
    hasComplement (Equal a b) = Not (Equal a b) `elem` assumptions
    hasComplement (Not proposition) = proposition `elem` assumptions
    hasComplement _ = False

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
  where
    relation operator a b =
      "(" ++ prettyTerm a ++ " " ++ operator ++ " " ++ prettyTerm b ++ ")"

-- Book examples paired with optional facts used by the theorem prover.
exampleSpecs :: [(String, String, [Formula])]
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
    , [ LessEqual (Variable "Y") (Variable "X")
          `Implies` Equal (Variable "X") (Maximum (Variable "X") (Variable "Y"))
      , Less (Variable "X") (Variable "Y")
          `Implies` Equal (Variable "Y") (Maximum (Variable "X") (Variable "Y"))
      ]
    )
  ]
