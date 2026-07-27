import PrisonersDilemma.Program
import PrisonersDilemma.Dynamics
import PrisonersDilemma.ProofSystem
import PrisonersDilemma.BaseTheorems
import PrisonersDilemma.Theorems.CupodBot
import Mathlib.Data.Nat.Log

/-!
# Spike S1 — does `boundedLob` typecheck? (recursion on the budget `k`)

Companion to `Research/Notes/DeadEnds/CONSTRUCTIVE_BOUNDED_LOB.md` §5, step **S1**.

**Goal of S1 (and ONLY S1):** confirm Lean 4 accepts the productive bounded-Löb
combinator — *strong recursion on the budget `k`* — as a total, well-founded definition.
This tests the **recursion**, not the math. No soundness, no real `Derivation`, no `eval`.

**Not imported by the root** (`PrisonersDilemma.lean`), so the green build is untouched.
Build this file alone with:

    lake env lean PrisonersDilemma/Research/Spikes/BoundedLobSpike.lean

A clean exit (no errors) == S1 passes.

We deliberately use a **toy** `ProofTerm φ k` (an opaque size-indexed carrier) rather than
the real `Derivation`, because S1 only asks "is the recursion well-founded?". The toy is
shaped so the real `Derivation`-backed version (S3) is a drop-in: same `step` signature,
same recursion skeleton.
-/

namespace PD.Spike
open PD

/-! ## 1. A toy size-indexed proof carrier

`ProofTerm φ k` stands in for "there is a proof of `φ` of size ≤ k". In the real engine
(S3) this becomes `{ d : Derivation φ // d.size ≤ k }` (or a genuinely size-indexed
`Derivation φ k`). Here it is just an inductive carrier so the recursion can be checked.

We give it ONE introduction that mirrors the only thing `boundedLob` needs to *build*: a
term at budget `k` assembled from (the promise of) terms at every smaller budget. That is
exactly the `search_t` / `searchBranch` discharge shape — "use the sub-proofs the guard
consumed at its smaller budget". -/

/-- Toy carrier: "a size-≤-`k` proof of `φ`". Opaque on purpose for S1. -/
inductive ProofTerm : Formula → Nat → Type where
  /-- Base: at budget `0` we can still *posit* a proof carrier (the toy stand-in for a
      leaf step like `.const`). Real engine: a 0-budget atom/const certificate. -/
  | leaf (φ : Formula) : ProofTerm φ 0
  /-- The discharge step, abstracted: given proofs at every smaller budget `j < k`,
      assemble one at budget `k`. This is the toy of "transcribe the guard's sub-proofs
      (consumed at budget `< k` thanks to `c_guard ≥ 1`) into my conclusion". -/
  | node (φ : Formula) (k : Nat) (sub : ∀ j, j < k → ProofTerm φ j) : ProofTerm φ k

/-! ## 2. The combinator — strong recursion on `k`

This is THE thing S1 exists to check. The `step` argument is the constructive,
budget-decreasing discharge: at budget `k`, given proof carriers at every `j < k`, it
produces a carrier at `k`. `boundedLob` ties the knot by *well-founded recursion on `k`*. -/

/-- **Constructive bounded Löb (toy).** Given a budget-decreasing discharge `step`, build a
    `ProofTerm φ k` for every `k`. The recursion is on `k` (well-founded on `Nat`), NOT on
    the program — which is the whole point: `DecMeasure.lean` refuted program-recursion;
    budget-recursion terminates because each guard strictly lowers the budget. -/
def boundedLob (φ : Formula)
    (step : ∀ k, (∀ j, j < k → ProofTerm φ j) → ProofTerm φ k) :
    ∀ k, ProofTerm φ k
  | k => step k (fun j _ => boundedLob φ step j)
  termination_by k => k
  decreasing_by exact ‹j < k›

/-! ## 3. Sanity checks — the combinator is usable and reduces

If these elaborate, the recursion is genuinely total (not just accepted as `partial`). -/

-- The trivial discharge that ignores the smaller-budget proofs and emits a leaf-or-node:
-- shows `boundedLob` can be *instantiated* and *applied*.
example (φ : Formula) : ProofTerm φ 5 :=
  boundedLob φ (fun k sub => .node φ k sub) 5

-- The combinator unfolds via its generated equation lemma: `boundedLob φ step k = step k
-- (…)`. (Well-founded recursion does NOT reduce by `rfl` — it goes through
-- `WellFounded.fix` — so we use the auto-generated `boundedLob.eq_def`, the normal way to
-- unfold such a definition. That it HAS an equation lemma confirms it elaborated as a
-- genuine total recursive definition, not `partial`.)
example (φ : Formula) (step : ∀ k, (∀ j, j < k → ProofTerm φ j) → ProofTerm φ k) (k : Nat) :
    boundedLob φ step k = step k (fun j _ => boundedLob φ step j) := by
  rw [boundedLob]

/-! ## 4. Shape check against the REAL `step` for CUPOD (S3 preview, not proven here)

The S3 gate instantiates `boundedLob` with CUPOD self-play. The `step` there is built from
`cupod_loeb_premise` (`Theorems/CupodBot.lean`):

    □_k (CUPOD k plays D vs CUPOD k) → (CUPOD k plays D vs CUPOD k)      -- size 5·log2 k + 33 ≤ k

The crucial S3 obligation (NOT discharged in S1) is that the box antecedent `□_k ψ` is
discharged by proofs the guard consumed at budget `< k` — i.e. the guard's `c_guard k =
log2 k + 1 ≥ 1` overhead makes the premise budget STRICTLY smaller, feeding the `j < k`
argument of `step`. We record the budget-decrease obligation as a statement to be proven at
S3, here just to pin the cost-model claim in a checkable place: -/

/-- Cost-model lemma the S3 budget-decrease will rest on: the `.search` guard always costs
    at least one character, so a guard at budget `k` leaves the sub-proof a strictly smaller
    budget. (`c_guard k = log2 k + 1 ≥ 1`.) This is the `j < k` witness `step` will need. -/
theorem c_guard_pos (k : Nat) : 0 < Nat.log2 k + 1 := Nat.succ_pos _

end PD.Spike

/-! # Spike S3 — THE GATE: can `boundedLob` be instantiated for CUPOD self-play?

We now work against the **real** engine types (`Provable`, `interp`, `Derivation`), not the
toy. The question: does the existing `cupod_loeb_premise` discharge actually fit a
budget-decreasing `step`, so `boundedLob` builds the CUPOD fixpoint?

**First, the type reality check.** Write `φ := (CUPOD k plays D vs CUPOD k)`. Then:

* `cupod_loeb_premise` proves `Provable k (□_k φ → φ)`.
* `interp (□_k φ) = Provable k φ`  (Dynamics.lean:55)
* `interp (□_k φ → φ) = (Provable k φ → φ.interp)`  (Dynamics.lean:53)
* `Provable_sound` therefore gives the **meta-level step**:  `Provable k φ → φ.interp`.

So the real "discharge" has type `Provable k φ → φ.interp`, where `φ.interp` is a *play
witness* `∃ n, play n (CUPOD k)(CUPOD k) = some .D`.

**The wall, made precise.** The toy `boundedLob` needs `step : (∀ j<k, P j) → P k` with the
SAME predicate `P` in premise and conclusion, so the recursion can re-enter. But the real
discharge is **asymmetric in two ways**:

1. *Predicate mismatch*: premise is `Provable k φ` (a proof), conclusion is `φ.interp` (a
   play). You cannot feed the output back as the next input — `φ.interp ≠ Provable k φ`.
2. *Budget mismatch*: the antecedent box is `□_k φ` at the **same** budget `k`, not
   `□_j φ` for `j < k`. So even ignoring (1), there is no smaller-budget premise to recurse
   on. The `c_guard` decrease lives INSIDE the certificate of the implication
   (`searchBranch`'s size accounting), **not** in the antecedent's budget.

This is the honest S3 finding: **the design-note §2.2 `step` signature does NOT match the
CUPOD discharge.** `boundedLob`-on-budget as written cannot consume `cupod_loeb_premise`.
The recursion that the toy `boundedLob` performs has no counterpart here, because Critch's
PBLT closes the loop by the *diagonal lemma over a self-referential ψ*, which manufactures
the `Provable k φ` antecedent — the very non-constructive move `boundedLob` was meant to
avoid. We rediscover, concretely, that the antecedent `Provable k φ` is exactly what is
missing and cannot be conjured by budget-recursion alone.

Below: the actual instantiation attempt, with the gap marked by `sorry`, so the type error
is explicit and checkable rather than rhetorical. -/

namespace PD.SpikeS3
open PD PD.Bots PD.BaseTheorems PD.Theorems

/-- The CUPOD self-play fixpoint formula. -/
def cupodφ (k : Nat) : Formula := .plays (CupodBot k) (CupodBot k) .D

/-- The real discharge extracted from `cupod_loeb_premise` + `Provable_sound`:
    `Provable k φ → φ.interp`. This is what the engine actually gives us — and it
    typechecks, confirming the meta-step exists. -/
theorem cupod_step :
    ∃ K₀ : Nat, ∀ k : Nat, k ≥ K₀ →
      (Provable k (cupodφ k) → (cupodφ k).interp) := by
  obtain ⟨K₀, hK₀⟩ := cupod_loeb_premise
  refine ⟨K₀, fun k hk hPk => ?_⟩
  -- `hK₀ k hk : Provable k (□_k φ → φ)`. Its interp is `Provable k φ → φ.interp`.
  have himpl : (Provable k (cupodφ k)) → (cupodφ k).interp := by
    have h := Provable_sound _ _ (hK₀ k hk)
    -- `interp (□_k φ → φ)` unfolds to `Provable k φ → φ.interp`.
    simpa [Formula.interp, cupodφ] using h
  exact himpl hPk

/-- **The gate, stated as the thing budget-recursion would need.** To run `boundedLob` we
    would need, at budget `k`, to PRODUCE the antecedent `Provable k (cupodφ k)` — ideally
    from strictly-smaller-budget data. This is precisely what is NOT available: the loop
    closes only via the (non-constructive) self-referential antecedent. We leave the gap as
    `sorry` to make the missing obligation explicit and machine-visible. -/
theorem cupod_antecedent_is_the_gap :
    ∃ K₀ : Nat, ∀ k : Nat, k ≥ K₀ → Provable k (cupodφ k) := by
  sorry

/-- Given the gap, the fixpoint follows trivially — confirming the gap IS the whole
    content (everything else typechecks around it). -/
theorem cupod_fixpoint_modulo_gap :
    ∃ K₀ : Nat, ∀ k : Nat, k ≥ K₀ → (cupodφ k).interp := by
  obtain ⟨K₁, hStep⟩ := cupod_step
  obtain ⟨K₂, hGap⟩ := cupod_antecedent_is_the_gap
  refine ⟨max K₁ K₂, fun k hk => ?_⟩
  exact hStep k (le_trans (le_max_left _ _) hk) (hGap k (le_trans (le_max_right _ _) hk))

end PD.SpikeS3

/-! # Spike S3′ — is the antecedent box budget forced to equal the conclusion's?

The S3 finding reduced the whole route to ONE arithmetic question: can the CUPOD discharge
be restated as `□_{k'} φ → φ` with `k' < k` STRICTLY (giving budget-recursion a foothold),
or is `k' = k` forced by the semantics?

**The answer is read directly off `eval` (Dynamics.lean:34–37):**

```
| .search k φ p q => if proofSearch k (φ.subst me opponent) then … p else … q
```

CUPOD `= .search k (opp plays self D) (.const D) (.const C)`. So when CUPOD runs, `eval`
consults `proofSearch k` — at **the bot's own parameter `k`, nothing smaller.** The guard
fires *iff* `Provable k (guard.subst …)`. Therefore the SOUND box premise — the one
`searchBranch` states and the one `eval` actually checks — is `□_k`, with the **same** `k`
as the bot's search budget. There is no `k' < k`: the bot searches at exactly `k`.

We make this machine-checked below. The point is not a new theorem but to PIN the claim
"`k' = k` is forced" to the kernel, so the design conclusion rests on a checked fact. -/

namespace PD.SpikeS3prime
open PD PD.Bots

/-- `CupodBot k`'s search node carries budget `k` *definitionally*: its guard is consulted
    at `k`, not at any `k' < k`. This is the formula whose provability `eval` tests. -/
example (k : Nat) :
    CupodBot k = .search k (.plays .opp .self .D) (.const .D) (.const .C) := rfl

/-- **The S3′ verdict, machine-checked.** When `CupodBot k` plays, the action is decided by
    `proofSearch k (…)` — the budget index is literally the bot's `k`. We show the eval step
    reduces to a branch on `proofSearch k`, i.e. there is no smaller budget `k'` anywhere in
    the semantics that could serve as a strictly-smaller antecedent box. -/
example (k n : Nat) (me other : Prog) :
    eval (n+1) me other (CupodBot k)
      = (if proofSearch k ((Formula.plays .opp .self .D).subst me other)
           then eval n me other (.const .D) else eval n me other (.const .C)) := by
  rfl

/-! **Conclusion of S3′.** `k' = k` is **forced** by `eval`'s `.search` rule: the guard is
consulted at the bot's own budget `k`. The `c_guard k` cost the certificate spends reading
the guard does NOT lower the *box* budget — it is internal proof-length bookkeeping, paid
on top of the atom, never subtracted from the antecedent's `k`. So:

> **The antecedent `Provable k φ` is irreducibly at budget `k`. There is no
> strictly-smaller-budget premise. Budget-recursion has no foothold. S3′ FAILS.**

This is not a defect to be engineered around — it is faithful to Critch: the bot genuinely
searches proofs of length ≤ k, and at the self-play fixpoint the only proof of cooperation
that exists is one that already assumes it (the diagonal/Löb fixpoint). Constructive
budget-recursion cannot manufacture it. **The honest ceiling for (B) is reached; route (A) —
faithful PBLT as an axiom (or as Critch's classical chain) — is what remains.** See the note
§7/§6 (updated) for the consequence. -/

end PD.SpikeS3prime
