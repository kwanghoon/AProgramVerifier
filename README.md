# A Simple Program Verifier in Haskell

This project implements the Chapter 10 theorem prover and Chapter 11
verification-condition generator for annotated WHILE programs. Specifications
use a Lisp-style S-expression syntax. The prover is a small rule-based system,
not a general-purpose arithmetic theorem prover; unsupported obligations are
reported rather than silently accepted.

## Run

```text
cabal run verifier
cabal test
```

The executable opens a menu with the Chapter 11 examples and option `9` for
the Chapter 10 theorem prover. Select a verifier example to display its
annotated program, generated verification conditions, and proof results. In
the theorem prover, enter a formula such as `(1 = 1)` or `(X = Y)`; type
`back` to return to the menu. Enter `0` or `q` at the main menu to exit.

## Supported WHILE language

A partial-correctness specification has the form:

```text
(SPEC precondition command postcondition)
```

Commands are `ASSIGN`, `SEQ`, `BLOCK`, annotated `WHILE`, annotated `FOR`, and
`IF2`. An `ASSERT` in a sequence gives the assertion between commands; loop
annotations are also written as `(ASSERT formula)`. A non-assignment command
in a sequence must have an annotation. `FOR` additionally checks that its
index and bounds are not assigned in its body.

Terms support integer literals, variables, `+`, `-`, `*`, `DIV`, unary `-`,
and `(max left right)`. Formulas support `T`, `F`, `NIL`, `=`, `<`, `<=`, `>`,
`>=`, `and`, `not`, and `implies`. Boolean connectives can use the examples'
prefix or infix Lisp-style forms, such as `(and P Q)` or `(P and Q)`.

The VC generator applies assignment substitution, annotated-sequence rules,
loop-invariant rules, and the bounded-loop entry, exit, and empty-range checks.

## Proving formulas

Use the exported functions directly, without constructing a WHILE program:

```haskell
proveText "((X + 0) = X)"  -- Right True
proveText "(X = Y)"        -- Right False (not provable from the defaults)
```

`prove` accepts an already constructed `Formula`; `proveText` parses a formula
string. Both automatically use `defaultFacts`, which combines `logicFacts` and
`arithmeticFacts`.

## Rewrite facts

The built-in fact sets are written as Lisp-style equations, matching the
Chapter 10 presentation. For example:

```text
((X + 0) = X)
((X = X) = T)
```

`parseFact` and `parseFacts` parse these equations into `Fact` values and infer
whether each side is a term or formula. Term equations are applied in their
written direction during normalization, while an equality goal can match a
term equation in either direction. A rewrite that immediately reverses itself
is not used for normalization, avoiding cycles such as commutativity; the
built-in arithmetic facts include addition and multiplication commutativity.
Formula equations are directed formula rewrites. Variables in fact patterns
are metavariables: a variable in a term position matches a term, while a bare
variable in a formula position matches a formula.

Applications can add rules by constructing `Fact` values and passing them to
`verifyText` or `verifySpec`. The maximum example in `exampleSpecs` supplies
facts like this:

```haskell
FormulaImplication
  (LessEqual (Variable "Y") (Variable "X"))
  (Equal (Variable "X") (Maximum (Variable "X") (Variable "Y")))
```

The parser also accepts explicitly tagged facts: `TERM-REWRITE`,
`TERM-EQUATION`, `FORMULA-REWRITE`, and `FORMULA-IMPLIES`. These are useful
when the intended fact kind is ambiguous or when a fact has implication
premises. The built-in lists use the untagged equation form.
