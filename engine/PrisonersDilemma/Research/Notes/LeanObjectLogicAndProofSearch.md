# Lean, Object Logic, and Proof Search in This Project

## Lean is the metalanguage

Lean is not automatically the proof system `S` from the Critch paper, and it is
not automatically the semantics of the agents' formulas.

In this project, Lean is the external mathematical language in which we define
and reason about everything else:

- the syntax of agents, `Prog`
- the syntax of formulas, `Formula`
- the operational behavior of agents, `eval`, `play`, and `outcome`
- the semantic interpretation of formulas, `Formula.interp`
- the abstract proof system interface, through `ProofWitness`,
  `witnessProves`, and `proofSearch`
- axioms connecting proof search, proof witnesses, and truth

So Lean is the meta-system. It checks our reasoning about the object language,
the proof system, and the semantics.

## The object language

The object language is the language that agents reason about. In this project,
it is the inductive type `Formula`:

```lean
inductive Formula where
  | plays : Prog -> Prog -> Action -> Formula
  | impl  : Formula -> Formula -> Formula
  | neg   : Formula -> Formula
  | box   : Nat -> Formula -> Formula
```

This is syntax. A term like:

```lean
Formula.plays OBot (CupodBot k) Action.D
```

is a piece of object-language syntax saying that `OBot` plays `D` against
`CupodBot k`.

The object language is not currently full first-order logic. It has implication,
negation, bounded provability boxes, and special atomic formulas of the form
`plays p q a`. Parameters such as `k` in `fun k => ...` live in Lean's
meta-language, not inside the object language as quantified variables.

## Semantics and truth

Semantics says what object-language formulas mean. In this project, semantics is
given by:

```lean
Formula.interp : Formula -> Prop
```

A formula is thus "true" if it is accepted by lean as `Formula.interp`.

This maps a `Formula` into a Lean proposition.

For example:

```lean
(Formula.plays p q a).interp
```

means:

```lean
exists n, play n p q = some a
```

So the object-language sentence "`p` plays `a` against `q`" is interpreted as a
Lean-level claim about the evaluator.

For implication:

```lean
(Formula.impl phi psi).interp
```

means:

```lean
phi.interp -> psi.interp
```

For bounded provability:

```lean
(Formula.box k phi).interp
```

means:

```lean
proofSearch k phi = true
```

Thus `.interp` is the bridge from object-language formulas to Lean-level truth.

## Syntax and proof

Syntax is about formal proofs, not truth assignments or semantic meaning.

In a usual logic course, we might define a proof system with axioms and rules:
for example, Hilbert-style axioms plus modus ponens. Then `S |- phi` means that
there is a formal derivation of `phi` in the proof system `S`.

In this project, we do not currently implement a concrete Hilbert system,
natural deduction system, or Peano arithmetic. Instead, the proof system `S` is
represented abstractly by:

```lean
axiom ProofWitness : Type
axiom witnessProves : ProofWitness -> Formula -> Prop
axiom witnessChars : ProofWitness -> Nat
```

Here:

```lean
witnessProves w phi
```

means that `w` is a formal proof witness for `phi` in the abstract proof system.

Unbounded derivability in `S` can be thought of as:

```lean
exists w, witnessProves w phi
```

or equivalently, using proof search:

```lean
exists m, proofSearch m phi = true
```

The proof system itself is therefore not concretely defined. It is axiomatized.

## Bounded proof search

The oracle:

```lean
proofSearch : Nat -> Formula -> Bool
```

models bounded proof search.

The statement:

```lean
proofSearch k phi = true
```

means that `phi` has a proof whose size fits within budget `k`.

This is connected to proof witnesses by:

```lean
proofSearch_spec :
  proofSearch k phi = true <->
    exists w, witnessProves w phi /\ witnessChars w <= k
```

So `proofSearch k phi = true` is a syntactic/proof-theoretic claim: the system
has found, or at least there exists, a bounded proof of `phi`.

It is different from:

```lean
phi.interp
```

which says that `phi` is semantically true.

## Soundness: from proof to truth

The key bridge from syntax to semantics is soundness:

```lean
witness_sound :
  witnessProves w phi -> phi.interp
```

Together with `proofSearch_spec`, this gives:

```lean
proofSearch_sound :
  proofSearch k phi = true -> phi.interp
```

In words:

If bounded proof search proves `phi`, then `phi` is true under the semantic
interpretation.

This is a bridge that Lean can use because it is stated as an axiom/theorem in
Lean.

## Completeness is limited

The reverse direction is not generally available:

```lean
phi.interp -> exists k, proofSearch k phi = true
```

This is not assumed for all formulas.

The project currently has a completeness principle only for atomic `plays`
formulas:

```lean
witness_complete_plays :
  forall p q a,
    (exists n, play n p q = some a) ->
      exists w, witnessProves w (Formula.plays p q a)
```

This says: if a play fact is semantically true, then the abstract proof system
can prove that play fact.

## `S derives phi` versus `box k phi`

There are several related but distinct claims:

```lean
exists m, proofSearch m phi = true
```

means `S` derives `phi` with some finite proof size.

```lean
proofSearch k phi = true
```

means `phi` is provable within the specific budget `k`.

```lean
Formula.box k phi
```

is the object-language formula saying "`phi` has a proof of size at most `k`."

Its semantics is:

```lean
(Formula.box k phi).interp = (proofSearch k phi = true)
```

Finally:

```lean
exists m, proofSearch m (Formula.box k phi) = true
```

means that `S` proves the boxed statement itself: `S` proves that `phi` has a
proof within budget `k`.

So there are two levels in a statement like:

```lean
proofSearch m (Formula.box k phi) = true
```

- `m` is the budget for proving the boxed formula
- `k` is the budget mentioned inside the boxed formula

## The Critch proof system `S`

In the Critch paper, `S` is a sufficiently strong formal proof system. It can
reason about arithmetic, proof lengths, programs, and bounded provability.

In this project, `S` is not explicitly constructed. Instead, it is represented
abstractly by:

- `ProofWitness`
- `witnessProves`
- `witnessChars`
- `proofSearch`
- axioms such as `proofSearch_spec`, `witness_sound`, and `PBLT`

This is why the current formalization is best understood as modeling the
properties we need from `S`, rather than implementing `S` itself.

## The PBLT issue

Critch's PBLT hypothesis says, informally:

```text
S proves: for all sufficiently large k,
  if p[k] is provable within f(k), then p[k].
```

That is a uniform proof of a quantified statement:

```text
S |- forall k > k1, box_{f(k)} p[k] -> p[k]
```

The current project often represents this kind of statement pointwise:

```lean
forall k, k > k1 ->
  exists m, proofSearch m (Formula.impl (Formula.box (f k) (phi k)) (phi k)) = true
```

This says: for each concrete `k`, there is some proof of the instance.

That is weaker/different as a formal encoding of the paper. The paper's version
is uniform; the current encoding is instance-by-instance.

A more faithful formalization would introduce a notion like:

```lean
uniformDerivesAfter : Nat -> (Nat -> Formula) -> Prop
```

to represent one proof, or one proof schema, of all sufficiently large
instances.

## Summary

The project has four layers:

```text
Lean metalanguage
  Defines and checks everything below.

Object language
  Formula, Prog, Action.

Abstract proof system S
  ProofWitness, witnessProves, witnessChars, proofSearch.

Semantics
  Formula.interp, play, eval, outcome.
```

The most important bridges are:

```lean
Formula.interp : Formula -> Prop
```

which maps object-language formulas to Lean propositions, and:

```lean
proofSearch_sound :
  proofSearch k phi = true -> phi.interp
```

which says that syntactic bounded provability implies semantic truth.

