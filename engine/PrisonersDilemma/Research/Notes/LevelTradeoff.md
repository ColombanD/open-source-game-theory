# Level 2 vs Level 3: Tradeoff Analysis

Companion note to [MakingSExplicit.md](MakingSExplicit.md), which lays out three
possible paths for making the proof system `S` explicit:

1. Narrow axiom (just the CUPOD self-fulfilling implication).
2. Semi-explicit proof system (program-specific axiom schemas + structural rules).
3. Fully explicit object theory (inductive `Proof` type, arithmetic, eval axioms).

This note records where the current axioms sit and what it would cost to push
further.

## Where the current axioms sit

The three axioms recently added to `Axioms.lean`:

- `proof_system_verifies_search_branch` — schematic over any agent whose source
  is `.search k ψ (.const a) (.const b)`, against any opponent.
- `proof_system_verifies_sim` — analogue for the `.sim` constructor.
- `proofSearch_impl_trans` — hypothetical syllogism in `S`.

These are **squarely level 2**. They are program-specific axiom schemas
describing what `S` can verify by inspecting source code (the `.search` and
`.sim` constructors), plus one structural rule. They generalize the previous
narrow `proofSearch_CupodBot_self_fulfilling` axiom: CUPOD-vs-CUPOD becomes the
instance `me = opponent = CupodBot k`.

The narrow axiom should be derivable from `proof_system_verifies_search_branch`
once `ψ.subst me opponent` matches the closed guard formula CUPOD feeds to
`proofSearch` at runtime. Worth verifying as a sanity check before relying on
the schemas for cross-pairings (CUPOD vs MirrorBot, DUPOC, etc.).

This is **not level 3**. Level 3 would require defining
`inductive Proof : Formula → Type`, proof sizes, modus ponens, axiom schemas
for propositional/modal/quantifier reasoning, and a soundness/completeness
bridge to `proofSearch`. None of that is present.

## What level 3 actually costs

To make `S` fully explicit:

1. **Object language with arithmetic and quantifiers.** Current `Formula` has
   `plays`, `box`, `impl`, `and`, `or`, `not` — no `∀`, no `∃`, no terms, no
   equality between programs. CUPOD's guard mentions source code and equality;
   currently finessed via `Formula.plays`. A real `S` needs to talk about
   programs as syntactic objects (Gödel-numbering or equivalent).

2. **Inductive `Proof : Formula → Type` with proof sizes.** Modus ponens,
   propositional + modal axiom schemas (K, necessitation), quantifier rules,
   equality, induction. Tractable but real Lean work — roughly 1–2k lines.

3. **Program-evaluation axioms inside `S`.** `S` must derive things like "if
   `eval` on this source returns `D` then `plays … D`." Either embed
   `Prog`/`eval` as defined predicates and prove the recursion equations as
   theorems of `S`, or add axiom schemas mirroring each `eval` rule. The
   principled option (former) is where most of the work lives.

4. **Bridge `proofSearch k φ = true ↔ ∃ p : Proof φ, proofSize p ≤ k`.**
   Implementing `proofSearch` as a bounded enumerator over `Proof` and proving
   it correct. Decidable, fiddly.

5. **Re-derive the CUPOD self-fulfilling implication inside `S`.** The payoff:
   `proof_system_verifies_search_branch` becomes a *theorem*, not an axiom.

Rough scale: comparable to formalizing a small fragment of PA + a Hoare-style
program logic. Published Lean/Coq projects in this neighborhood (Gödel
incompleteness in Coq, Paulson in Isabelle) are multi-person-year efforts. A
minimal version tailored to `Prog` only is smaller — maybe 2–4k lines and a
few focused months — but still a real project.

## The actual tradeoff

**Level 2** gives every CUPOD-style theorem currently needed, with axioms
whose informal justification is one sentence ("S can read source code"). The
schemas are quantified over program structure, not specific bots, so they
scale to MirrorBot, DUPOC, cross-pairings without further axioms.

**Level 3** turns those axioms into theorems and answers "what exactly does
`S` need to be?" with a concrete inductive type. The cost is that the bulk of
the formalization shifts from game theory to proof theory.

## Recommendation

Stay at level 2 unless the advisor wants proof-theoretic content. The level-2
axioms are honest: labeled, justified by source-code inspection, isomorphic to
moves Critch makes silently in the paper. Defensible for a thesis on
game-theoretic content.

Possible middle hedge: keep level 2, add a short section sketching the
inductive `Proof` type and which axioms would become theorems. Demonstrates
understanding of the gap without paying to close it.

## Sketch: unifying the source-inspection axioms

`proof_system_verifies_search_branch` and `proof_system_verifies_sim` are both
instances of the same idea:

> `eval` tells you *when* an agent plays `a`. The axiom says `S` knows this too.

More precisely: look at the `eval` case for a constructor, find the condition
under which it returns `a`, and call that `Φ`. The axiom says `S` proves
`Φ → plays me opp a`.

For `.search k ψ (.const a) (.const b)`: `eval` returns `a` exactly when
`proofSearch k (ψ.subst me opp) = true`, i.e. when `□_k (ψ.subst me opp)`
holds. So `Φ = □_k (ψ.subst me opp)` and the axiom says:

```
S proves:  □_k (ψ.subst me opp)  →  plays me opp a
```

For `.sim p q`: `eval` returns `a` when `p.subst me opp` plays `a` against
`q.subst me opp`. So `Φ = plays (p.subst me opp) (q.subst me opp) a` and the
axiom says:

```
S proves:  plays (p.subst me opp) (q.subst me opp) a  →  plays me opp a
```

In both cases the content is the same: **`S` can perform one step of reading
`eval`'s source code for that constructor.** A unified schema names this
pattern once instead of once per constructor. Sketch:

```lean
/--
A "source-inspection step" for a constructor of `Prog`. Records, for each
bot shape, the formula `Φ` that `eval` reduces playing-`a`-against-`opp` to.

* `shape : Prog` — a pattern like `.search k ψ (.const a) (.const b)` or
  `.sim p q`, possibly with metavariables for sub-programs.
* `reduct me opp a` — the formula `eval` produces after one step of
  unfolding `me = shape` against `opp`.
-/
structure EvalStep where
  shape  : Prog
  reduct : Prog → Prog → Action → Formula

/-- The two current axioms as `EvalStep` values. -/
def searchStep (k : Nat) (ψ : Formula) (a b : Action) : EvalStep :=
  { shape  := .search k ψ (.const a) (.const b)
    reduct := fun me opp _ => .box k (ψ.subst me opp) }

def simStep (p q : Prog) : EvalStep :=
  { shape  := .sim p q
    reduct := fun me opp a =>
      .plays (p.subst me opp) (q.subst me opp) a }

/--
Source-code reflection: for any `EvalStep` whose `shape` is `me`'s literal
source, `S` proves the reduct implies the play. Subsumes
`proof_system_verifies_search_branch` and `proof_system_verifies_sim`.
-/
axiom proof_system_verifies_eval_step :
  ∀ (step : EvalStep) (me opp : Prog) (a : Action),
    me = step.shape →
    ∃ m, proofSearch m
      (.impl (step.reduct me opp a) (.plays me opp a)) = true
```

What this buys: one axiom instead of N, and the *informal* justification
("S faithfully reflects one `eval` step per constructor") is stated once.
Adding a new constructor means adding a new `EvalStep`, not a new axiom.

What it doesn't buy: the schema is still axiomatic. It does not justify
*why* `S` reflects `eval` — that justification still lives in prose. To get
the schema as a *theorem*, you'd need level 3: embed `eval` as a defined
predicate in `S`, prove the recursion equations, and derive each
`EvalStep`'s implication from those equations. At that point
`proof_system_verifies_eval_step` becomes a meta-theorem about the family.

Awkwardness at level 2: the `reduct` field is a Lean function returning a
`Formula`, but it morally encodes a piece of `S`'s syntax. Without a real
object language this conflates meta-level computation with object-level
formula construction. Workable, but slightly dishonest — every `EvalStep`
implicitly assumes `S` can express whatever `reduct` happens to compute.
The per-constructor axioms hide this by spelling out a fixed formula
shape; the unified schema makes it visible.

Verdict: worth doing if a third or fourth constructor axiom shows up,
otherwise the per-constructor form is fine.