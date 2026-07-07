# Normalization for a Bounded-Löb Modal Proof Calculus (the D2f-b theorem)

*Status 2026-07-03: precisely stated, attack fully mapped, three-lemma proof plan below.
This is the ONLY remaining gap in the T4.1b CutRelevance pipeline — and plausibly a
stand-alone publishable result. Everything referenced is kernel-checked in
`Research/Spikes/transcript/T49TreeSubstrate.lean` unless marked OPEN.*

## 1. The object

The calculus is `Provable` (Derivation.lean): a bounded provability logic with
transcript-cumulative budgets, whose modal fragment is GL-like — `boxIntro` (bounded
necessitation), `axK`/`axKf` (K-distribution), `box4`, `boxMono`, and the Löb fixpoint
pair `diagF`/`diagB` for the sentence `.diag g tgt` — plus a Hilbert implication layer
with composition (`implTrans`), the S-combinator (`impS2` — CONTRACTION), and weakening
(`weakenImpl`). `ProvT` is its Type-valued mirror (exact: `Provable_iff_nonempty_ProvT`).

The machine (`boxInvGo`) is a Krivine-style spine evaluator: state `(t, S)` with `t` a
proof tree and `S` a dependent stack of discharges for `t`'s implication spine; push at
`app`, drop at `weakenImpl`, compose at `implTrans`, DUPLICATE the head at `impS2`,
unfold at `diagF` (extract the diag discharge's content, walk it), consume at modal
leaves. It is fuel-indexed and correct by construction: every `some` is a content tree
within the box's subscript.

## 2. The theorem (OPEN)

**BoxInvTotal**: for every `t : ProvT m (.box c ψ)` there is fuel on which
`boxInv fuel t` returns `some`.

Equivalently: the machine weakly normalizes on all well-typed states with box/diag cores.

## 3. What is already proven (the fenced perimeter)

| Fact | Name | Meaning |
|---|---|---|
| Contraction-free totality | `boxInvGo_total`, `boxInv_total_of_freeS2` | halts at fuel `(wt t+1)² + wt t + 1` when no `impS2` occurs |
| Weight conservation | `boxInvGo_wt_le` | results weigh ≤ consumed state (fails on `impS2` — hypotheses exact) |
| Diet preservation | `boxInvGo_gateOK` | extraction never leaks exotic cuts (holds even WITH `impS2`) |
| Depth conservation | `boxInvGo_s2d_le` | extraction never builds an `impS2` |
| Budget bounds weight | `ProvT.wt_le_budget` | every gate pays ≥ 1 character per walkable node |
| **The quantitative Löb cap** | `content_wt_le_subscript` | box contents weigh ≤ their own subscript |
| Unreachability of `none` arms | inside `boxInvGo_total` | via `IsCore`, stack index chasing, `derivation_shape` |

The Löb cap is the reason the theorem should be TRUE: every unfolding of
`□g(.diag g tgt)` along a run yields material of weight ≤ g — the SAME `g`, pinned by
the formula — so Löb unfold-chains at a fixed diag formula are weight-capped even though
the formula recurs. Boundedness is what restores normalization to a GL-like logic.

## 4. The route-map — techniques that provably fail (do not retry)

1. **Local-charge potentials** (linear / multiplicative / semi-multiplicative stack
   potentials with per-node charges): contraction cost depends on the discharged
   material, unknown at the node; stack×stack products at `axKf` leaves and `diagF`
   continuations. Exact failure computations in `CUT_RELEVANCE.md` D2f-b entries.
2. **Tait on formula structure**: `.diag g tgt` unfolds to
   `.impl (.box g (.diag g tgt)) tgt` — a RECURSIVE type; formula recursion ill-founded.
3. **Type-order (arrow-depth) Gentzen ranks**: `order(diag) = ∞`, same reason.
4. **Step-indexed logical relations**: break the diag circle but prove safety, not
   termination.
5. **Budget- or weight-indexed Tait**: the arrow case must quantify over arguments of
   arbitrary weight/budget; no lex `(index, |ξ|)` founds the definition. (The
   biorthogonality fix in §5 addresses exactly this.)
6. **Counting/tower measures** (`#impS2`-weighted, `W^N`, towers): break on NESTED
   contraction — a fire duplicates a discharge of arbitrary internal count/depth.
7. **Syntactic fragments** (stack-monotone trees, depth ≤ 1): violated by
   `app(axKf-leaf, Löb-argument)` — the most common real pattern.
8. **Prop-level bypass** (master induction on `Provable` with `∃ tame tree` motive,
   using `Provable m (□cψ) → Provable c ψ` by soundness — a one-liner worth knowing):
   the wild-cut `app` case still requires crossing two tame trees, which is the same
   machine with the same contraction problem; and soundness-produced judgments are
   opaque to structural induction.
9. **Knaster–Tarski fixpoint for the diag truth-value**: the defining operator is
   ANTITONE (the diag occurs under two polarity flips through `impl`), no fixpoint.

## 5. The proof plan (reachability-Tait) — three lemmas

The residue of all failures points at one design: quantify the arrow case over
MACHINE-REACHABLE arguments only, not all trees. The machine is closed — every tree in
any reachable state is assembled from the initial material — and along any single run,
weight strictly decreases at every extraction. Concretely:

* **Lemma R (reachable closure).** Define `Reach(t₀)` — the set of (tree, stack) states
  reachable from `(t₀, nil)`, including dive sub-states — inductively over machine
  steps. Prove: every tree occurring in `Reach(t₀)` is an `app`/`boxIntro` assemblage
  over subtrees of `t₀` and extraction results thereof; multisets of original-subtree
  occurrences grow only at `impS2` fires. (Mechanical; the machine's arms are the
  induction.)
* **Lemma C (the computability predicate).** Define `Good` on `Reach(t₀)`-trees by
  recursion on the lexicographic (Löb-cap weight of the pinned unfolding budget, spine
  formula) — the arrow case quantifies over `Reach(t₀)`-arguments whose weight is
  bounded by Lemma R's invariant, which is what makes the definition well-founded where
  route 5 failed; the diag case recurses at content-weight ≤ g (the Löb cap), strictly
  below the consuming state's material. THIS IS THE HARD DESIGN: the exact index needs
  offline iteration — candidate: ordinal `ω·(unfold budget) + |spine formula|` over the
  reachable-argument restriction.
* **Lemma F (fundamental).** Every well-typed tree is `Good`, by induction on the tree
  (16 constructors), using Lemma C's closure conditions per arm — `impS2`'s arm is where
  contraction is paid by the quantification (both premise spines consume the SAME
  reachable discharge; `Good` of the discharge is a single hypothesis used twice — no
  measure needs to pre-pay it, which is exactly what all seven measure routes lacked).

Then `BoxInvTotal` = Lemma F at the root + `Good` unfolded at the box core.

**Effort estimate**: 2–4 dedicated sessions IF Lemma C's index closes on paper first;
genuine risk it needs ordinal-indexed machinery beyond that. Fallbacks unaffected:
`boxInv_total_of_freeS2` (contraction-free fragment, closed-form fuel) and the
executable per-instance pipeline (extract → check → `certify`) already deliver
zoo-scale CutRelevance certificates without this theorem.

## 6. THE SHARPEST FINDING (2026-07-03, the Lemma-C design attack): diag is a
NEGATIVE recursive type — this theorem is about defusing the Y-combinator

`.diag g tgt` satisfies `D ≅ (□g D) → tgt` with `D` in ANTECEDENT (negative) position.
That is the Curry/Y-combinator recipe: calculi with negative recursive types are NOT
normalizing in general (the untyped λ-calculus embeds), and the Löb fixpoint is
literally this pattern at the modal level — which is WHY unbounded GL-style proof
reduction fails to normalize, and why routes 2/3/9 (formula recursion, type order,
Tarski fixpoints) had to fail: they fail for Y too.

The bounded calculus escapes the Y-divergence through exactly two facts, both now
kernel-checked:
  * **the Löb cap** (`content_wt_le_subscript`): every unfolding of `□g D` yields
    material of weight ≤ g, pinned by the formula;
  * **strict consumption** (`boxInvGo_wt_lt`, T49 §18): extraction returns STRICTLY
    lighter material than the state it consumed — so a Y-loop cannot dynamically
    regenerate itself (and literal self-reference is impossible: trees are finite).

Consequently the truth-question is sharpened: an infinite run cannot be sustained by
Löb unfolding (strictly descending) nor by literal cycles (determinism + strictness);
the only remaining candidate engine of divergence is `impS2`-duplication feeding
unfoldings with fresh copies — and each fire consumes an `impS2` node of the walker
while copies are only ever re-fired inside strictly lighter or structurally smaller
walkers. We conjecture BoxInvTotal is TRUE, with the proof shape: Tait for the
contraction (∀-hypotheses make duplication free), the diag case broken by strict
consumption instead of formula descent. The remaining design gap is unchanged (Lemma
C's index across the arrow-quantification), but the negative-type diagnosis explains
every prior failure at once and pins the novelty: **boundedness defuses Y**.

## 7. Why it matters beyond the thesis

GL (provability logic) does not enjoy cut-elimination in the ordinary sense; the Löb
axiom is the obstruction. This engine's BOUNDED Löb — where every box carries a budget
and the fixpoint's unfolding is budget-pinned (`content_wt_le_subscript`) — appears to
restore normalization. A proof would be, to our knowledge, the first normalization
theorem for a bounded provability logic, with the bounded-Löb cap as its load-bearing
novelty. That is a paper regardless of the thesis timeline.
