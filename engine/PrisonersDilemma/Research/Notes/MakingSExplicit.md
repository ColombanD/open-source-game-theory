# Making the Proof System `S` Explicit

## The core issue

In Critch's CUPOD proof, the key step is that the formal proof system `S` can
verify that the CUPOD self-play formula is potentially self-fulfilling.

For CUPOD, the formula is:

```text
p[k] = "CUPOD(k)(CUPOD(k).source) == D"
```

The PBLT hypothesis requires:

```text
S proves: for all k > k1,
  box_{f(k)} p[k] -> p[k]
```

In the self-play theorem, `f(k) = k`, so this becomes:

```text
S proves: for all k > 0,
  box_k p[k] -> p[k]
```

Informally, this is true because CUPOD is constructed to make it true:

1. Assume `box_k p[k]`.
2. This means there is a proof of `p[k]` of length at most `k`.
3. `CUPOD(k)` searches for such a proof.
4. Therefore that proof search succeeds.
5. By CUPOD's source code, if the search succeeds, CUPOD returns `D`.
6. Therefore `p[k]`.

That is the self-fulfilling structure.

## Why this is not automatic in this project

The reasoning above is valid, but in Critch it is reasoning **inside the proof
system `S`**.

In the current Lean project, we can reproduce this reasoning in Lean's
meta-theory. For example, we can prove a semantic implication of the form:

```lean
(Formula.impl
  (Formula.box k psi)
  psi).interp
```

where:

```lean
psi = Formula.plays (CupodBot k) (CupodBot k) Action.D
```

This says:

```text
if `box_k psi` is semantically true, then `psi` is semantically true.
```

But the PBLT hypothesis needs a syntactic/proof-theoretic claim:

```lean
exists m,
  proofSearch m
    (Formula.impl (Formula.box k psi) psi) = true
```

This says:

```text
the proof system `S` proves the implication.
```

Those are different.

The semantic statement says:

```text
Lean can see that the implication is true.
```

The proof-search statement says:

```text
`S` has a proof of the implication.
```

The current project does not have a general bridge from semantic truth to
provability in `S`.

## What the current framework provides

The current proof-system interface is abstract:

```lean
ProofWitness : Type
witnessProves : ProofWitness -> Formula -> Prop
witnessChars : ProofWitness -> Nat
proofSearch : Nat -> Formula -> Bool
```

and:

```lean
proofSearch_spec :
  proofSearch k phi = true <->
    exists w, witnessProves w phi /\ witnessChars w <= k
```

This says what it means for bounded proof search to succeed.

The framework also has soundness:

```lean
proofSearch_sound :
  proofSearch k phi = true -> phi.interp
```

So if `S` proves a formula, then the formula is semantically true.

But the reverse is not available in general:

```lean
phi.interp -> exists k, proofSearch k phi = true
```

The project only has completeness for atomic `plays` formulas:

```lean
proofSearch_complete_plays :
  (exists n, play n p q = some a) ->
    exists k, proofSearch k (Formula.plays p q a) = true
```

This cannot prove:

```lean
exists m,
  proofSearch m
    (Formula.impl (Formula.box k psi) psi) = true
```

because the outer formula is an implication, not a `plays` formula.

## Why not add general reflection?

One tempting axiom would be:

```lean
forall k phi,
  exists m,
    proofSearch m (Formula.impl (Formula.box k phi) phi) = true
```

This says:

```text
S proves box_k phi -> phi for every formula phi.
```

That is too strong if `S` is supposed to behave like a realistic formal proof
system. It is a general reflection principle. In Gödel/Löb settings, systems
cannot usually prove their own unrestricted soundness without becoming
dangerously strong or inconsistent relative to their intended interpretation.

Critch's CUPOD proof does not need general reflection. It only needs the
specific implication for the CUPOD self-play formula.

## A safer narrow axiom

A narrow axiom matching the CUPOD proof would be:

```lean
axiom proofSearch_CupodBot_self_fulfilling :
  forall k,
    exists m,
      proofSearch m
        (Formula.impl
          (Formula.box k
            (Formula.plays (CupodBot k) (CupodBot k) Action.D))
          (Formula.plays (CupodBot k) (CupodBot k) Action.D)) = true
```

This says exactly:

```text
S proves that if CUPOD(k) can prove it defects against itself,
then CUPOD(k) defects against itself.
```

That is much closer to Critch's Theorem 3.4. It does not claim that `S` proves
arbitrary reflection principles.

## Why Critch can use this step

Critch assumes that `S` has enough expressive power to reason about:

- computable functions
- program source code
- proof checking
- proof lengths
- abbreviation expansion

Appendix B states assumptions of this kind. So when the paper says that `S`
can verify the self-fulfilling implication, it relies on these background
properties of `S`.

Our current Lean project has not implemented those properties. It has only
axiomatized an abstract proof-search interface.

Therefore, the Critch reasoning is not wrong. It is just not yet internalized
in our model of `S`.

## What it would mean to make `S` explicit

A more explicit `S` would define proofs directly, for example:

```lean
inductive Proof : Formula -> Type where
  | modusPonens :
      Proof (Formula.impl phi psi) ->
      Proof phi ->
      Proof psi
  | axiomK :
      Proof (Formula.impl phi (Formula.impl psi phi))
  | axiomS :
      Proof ...
```

Then one would define proof size:

```lean
proofSize : Proof phi -> Nat
```

and bounded derivability:

```lean
def DerivesWithin (k : Nat) (phi : Formula) : Prop :=
  exists p : Proof phi, proofSize p <= k
```

Then `proofSearch` could be connected to this concrete proof system:

```lean
proofSearch k phi = true <-> DerivesWithin k phi
```

To handle CUPOD, `S` would also need rules or axiom schemas allowing it to
reason about program evaluation. For example, it would need to prove facts
like:

```text
if the search guard in CUPOD(k) succeeds, then CUPOD(k) returns D.
```

This can be done at different levels of ambition.

## Three possible paths

### 1. Narrow axiom

Add only the CUPOD self-fulfilling axiom.

This is the simplest and closest to the exact theorem currently needed.

### 2. Semi-explicit proof system

Define an inductive proof system for propositional/modal reasoning, plus
selected program-specific axiom schemas such as CUPOD self-fulfillment.

This makes `S` more visible without formalizing all of arithmetic and program
verification.

### 3. Fully explicit object theory

Build an object language with arithmetic, quantifiers, program syntax, proof
checking, proof lengths, and evaluation predicates.

This is closest to Critch's assumptions, but it is a much larger
formalization project.

## The key distinction

The most important distinction is:

```text
Lean proves the implication is semantically true.
```

versus:

```text
S proves the implication.
```

The first is a meta-theoretic statement in Lean.

The second is an object-level proof-theoretic statement about the proof system
used by the agents.

Critch assumes enough about `S` to get the second from source-code reasoning.
Our current project does not yet encode those assumptions, so we either need a
narrow axiom or a more explicit proof system.

