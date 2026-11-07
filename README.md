# A Simple Program Verifier in Haskell

This project implements a small verifier for annotated WHILE programs using
the Lisp-style syntax of the chapter examples. It parses a partial-correctness
specification, generates verification conditions, and tries to prove them with
a deliberately bounded symbolic prover.

## Run

```text
cabal run verifier
cabal test
```

`cabal run verifier` opens a numbered menu. Select an example to display its
annotated WHILE specification, generated verification conditions, and proof
result. The menu returns after each run so examples can be tried individually
or repeatedly; enter `0` or `q` to exit.

The examples are an incorrect and corrected swap, integer division, the three
summation variants, and the maximum program with and without supplied facts.

## Supported language

Specifications have the form `(SPEC precondition command postcondition)`.
Commands include `ASSIGN`, `SEQ`, `BLOCK`, annotated `WHILE`, annotated `FOR`,
and `IF2`. An `ASSERT` inside a sequence supplies the assertion used between
commands; loop annotations are written as `(ASSERT formula)`. Expressions
support integer literals, variables, `+`, `-`, `*`, `DIV`, comparisons, `and`,
`not`, and `(max left right)`.

The VC generator applies assignment substitution, loop invariant rules, the
bounded-loop entry/exit/empty-range checks, and backward propagation through
annotated sequences. The prover handles propositional implications, integer
polynomial identities, consecutive-product division by two (needed for the
triangular-number example), and user-supplied implication facts. It is not a
general-purpose arithmetic theorem prover; unsupported obligations remain
visible as unproved VCs.
