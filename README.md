# Panproof

This repository contains a study project using `agda2hs`.
The study has two purposes:
1) To help me learn `agda2hs`
2) To be a minimal proof of concept for a flexible proof elaborator for proofs from automated reasoning systems. 

[Agda2hs](https://github.com/agda/agda2hs) is tool to generate idiomatic Haskell code from a subset
of Agda.  This is potentially useful to build high performance proof processing tools for automated
reasoning systems.

## What

The code has been tested with Agda version 2.7.0.1, `agda2hs` version
1.3, and `ghc` version 9.6.6.
To run it, install `agda2hs` using `cabal install agda2hs`.  Then,
generate the Haskell files from Agda by running the `genHaskell.sh` script
from the main folder.

Then `cabal run` prints a proof as a list of steps:
```bash
> cabal run Panproof
1 assert [] ⇒ ((and A) ((and A) (not (not ((or A) B)))))
2 use rule    andE3 on [1]	[] ⇒ (not (not ((or A) B)))
3 use axiom notnotE on [2]	[] ⇒ ((or A) B)
4 use rule    orSym on [3]	[] ⇒ ((or B) A)
```

Every line is an indexed step.
There are two distinct kinds of proof rules: an `axiom` is a axiom of propositional
logic, a `rule` is a derived proof rule.

This proof derives $B \lor A$ from $A \land A \land \neg \neg (A \lor B)$ using
two derived rules: a ternary conjunction elimination, and symmetry of disjunction.

Under the hood, this proof isn't simply printed.  Every step is also checked
by a formally verified proof checker.

The `andE3` rule is somewhat unorthodox, let's break it into two binary conjunction-elimination steps:
``` bash
> cabal run Panproof andE3
1 assert [] ⇒ ((and A) ((and A) (not (not ((or A) B)))))
2 use axiom   andE2 on [1]	[] ⇒ ((and A) (not (not ((or A) B))))
3 use axiom   andE2 on [2]	[] ⇒ (not (not ((or A) B)))
4 use axiom notnotE on [3]	[] ⇒ ((or A) B)
5 use rule    orSym on [4]	[] ⇒ ((or B) A)
```

Of course, this elaboration is also formally verified.  In fact, the existence
of the elaboration function is the proof of the correctness of the checker.
It's a bit like executing both "ends" of the Curry-Howard correspondence.

Of course, we can also turn `orSym` into a subproof:
```bash
> cabal run Panproof orSym
1 assert [] ⇒ ((and A) ((and A) (not (not ((or A) B)))))
2 use rule    andE3 on [1]	[] ⇒ (not (not ((or A) B)))
3 use axiom notnotE on [2]	[] ⇒ ((or A) B)
4 use axiom  assume on []	[A] ⇒ A
5 use axiom    orI2 on [4]	[A] ⇒ ((or B) A)
6 use axiom  assume on []	[B] ⇒ B
7 use axiom    orI1 on [6]	[B] ⇒ ((or B) A)
8 use axiom     orE on [7,5,3]	[] ⇒ ((or B) A)
```
or expand both:
```bash
cabal run Panproof orSym andE3
1 assert [] ⇒ ((and A) ((and A) (not (not ((or A) B)))))
2 use axiom   andE2 on [1]	[] ⇒ ((and A) (not (not ((or A) B))))
3 use axiom   andE2 on [2]	[] ⇒ (not (not ((or A) B)))
4 use axiom notnotE on [3]	[] ⇒ ((or A) B)
5 use axiom  assume on []	[A] ⇒ A
6 use axiom    orI2 on [5]	[A] ⇒ ((or B) A)
7 use axiom  assume on []	[B] ⇒ B
8 use axiom    orI1 on [7]	[B] ⇒ ((or B) A)
9 use axiom     orE on [8,6,4]	[] ⇒ ((or B) A)
```

Under the hood, this proof of concept implements a very simple
propositional logic with three fixed constants ($A$, $B$, $C$)

## Why? Solving the $n * (m + 1)$ problem.

Many automated reasoning systems, like SMT solvers and superposition provers, produce proofs to certify
their output.
Users of automated reasoning systems typically translate these proofs into their own logic.
For example, Isabelle/HOL doesn't accept proofs that were not replayed in its minimal reasoning kernel.
Some other applications trust the output of the automated reasoning systems, but independent proof checkers
can improve the trustworthiness of the output.

While the logics used most automated reasoning systems are remarkably similar, the calculi used by their
proof output vary widely, and often expose implementation details.  Hence, to check the proofs of $n$ automated
reasoning systems, and to integrate them with $m$ applications, we have to implement $n * (m + 1)$ translation
pipelines.

This repository is a proof-of-concept for a framework that can be used as a proof preprocessor to increase the
commonality of the proofs.  While the logic is fixed, we define **proof rules** in a flexible manner.
Note that becuase the logic itself is fixed, Panproof is not a logical framework.

As an Agda datatype:

```agda
data ProofRule (@0 Γ : Signature) : Set where
 Rule :
    (name : String)
  → (check     : (List (Sequent Γ) → Maybe (Sequent Γ)))
  → (elaborate : (prems : List (Sequent Γ)) → Maybe (Step Γ prems))
  → (@0 proof  : (prems : List (Sequent Γ))
               → (check prems) ≡ (checkStep (elaborate prems)))
  -------------------------------------------------------------------
  → ProofRule Γ
```

The `check` function computes a conclusion from a list of premises.
It is an *oracle*.  While it allows us to define rules in a flexible manner, it doesn't
justify the rules relative to the reference logic (given by $Γ$).
This is similar to proof rules in the [Eunoia](https://github.com/cvc5/ethos)
framework for SMT proofs.  It allows fast proof checking, but provides limited
assurance about the correctness of the rule, and doesn't help any consumer of
the proof output

The `elaborate` function, on the other hand, translates a proof step using the
rule into a proof tree.  This function provides strong assurance about
the correctness of the rule.  The type system guarantees that `elaborate`
cannot "go wrong".  This elaboration is similar to interactive theorem provers
like [HOL](https://hol-theorem-prover.org/).  Elaboration also helps consumers: it is enough
for them to understand the rules used by the elaboration.
However, elaboration is slower, and can lead to a blowup of the proof size.

[comment]: <> (TODO: What about recursive rules?)

Having both, `check` and `elaborate` gives us the best of both worlds.
If we need fast checking, we can use the `check` function.
If we want to elaborate a rule, we can use the `elaborate` function.
Note that a consumer can also flexibly choose which rules to elaborate.

How can we know that these two functions coincide?
This is ensured by the `proof` argument.  The author of the proof   must show that the conclusion generated by `check` is the same as the
result of checking the proof tree generated by `elaborate`.
This proof also provides us with assurances about `check`.  Since
`elaborate` cannot "go wrong", the proof shows that `check` cannot
produce conclusions that aren't entailed by the premises.

Note that `proof` is annotated with `@0`.  This is an *erasure* annotation, and indicates
that the proof is run-time irrelevant.   The `agda2hs` tool uses these annotations
to generate "natural" Haskell code from a subset of Agda.  This means we can potentially
get a high-performance proof checker.  For the example above, `agda2hs` generates
```haskell
data ProofRule = Rule String ([Sequent] -> Maybe Sequent)
                             ([Sequent] -> Maybe Step)
```

## File Structure

The proof of concept is structured as follows:

- `agda/Core/Terms.agda` defines an intrinsically typed propositional logic.
  To ensure that only well typed terms can be built by the Haskell side, we
   also define some safe functions, such as
   ```agda
   mkApp : ∀ (Γ : Signature) {@0 S₁ S₂ : Sort} → Γ :⊢ S₁ → Γ :⊢ S₂ → Maybe (Σ[ s ∈ Sort ] (Γ :⊢ s))
   ```
   This function builds an application term.  If successful, it returns its sort and the new term.
   This is translated into a correct-by-construction Haskell function
   ```haskell
   mkApp :: Signature -> Term -> Term -> Maybe (Sort, Term)
   ```
- `agda/Core/Proofs.agda` defines the notion of a sequent, proof steps, and proof rules.  It also
   defines a simple "reference checker" that is used to prove the equivalence of the checker and elaborator.
- `agda/Core/Rules.agda` defines some common axioms for propositional logic and the two rules for
  the example.
- `haskell/API.hs` defines a (partially) safe API by hiding "raw" functions generated from Agda.
- `haskell/Main.hs` contains an (ugly) proof checker and the example.
