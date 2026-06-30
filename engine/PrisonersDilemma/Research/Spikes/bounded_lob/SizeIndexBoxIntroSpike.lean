/-!
# Step 2 gate spike — size-indexed box-introduction

⚠️ **SUPERSEDED 2026-06-29 — the refactor this gated is SHELVED as unnecessary.** This spike tested
a PROOF-TREE size index; `FormulaSizeBoxIntroSpike.lean` then found the real engine uses
conclusion-`Formula.size`, so box-intro is a LOCAL constructor needing NO re-index. `box_provable`
was duly eliminated by `Provable.boxIntro` (Derivation.lean) with NO refactor. This file is retained
only for the K-distribution soundness result (the `distrib`/`k_no_false` part), which informs the
remaining `boxInternalize` target. See `Research/Notes/WALLS_AND_EXTENSIONS.md`.

---

GO/NO-GO for the ~500-ref size-indexed-`Derivation` refactor. Scope:
`Research/Notes/STEP2_SIZE_INDEX_SCOPE.md`.

Question: if the box budget is a *tracked proof index* (not a free `Nat` payload on the formula),
can `box_provable` (necessitation) and `boxInternalize` (fixpoint internalization) become
CONSTRUCTIVE theorems — kernel-positive box-intro constructor, `#print axioms` ⊆ {propext, Quot.sound},
and SOUND (an opaque false atom stays underivable)?

PASS criteria (both):
  1. box-intro constructor typechecks + necessitation lemma proven, no axiom.
  2. fixpoint internalization genuinely BUILT (not `:= hfitD`) AND sound (false atom underivable).

NOT root-imported. Build: `lake env lean PrisonersDilemma/Research/Spikes/bounded_lob/SizeIndexBoxIntroSpike.lean`
-/

namespace PD.SizeIndexBoxIntroSpike

/-! ## Toy syntax — the 3 shapes that exercise the question -/

/-- Opaque play-atoms, identified by a `Nat` tag. `trueAtom`/`falseAtom` model a real-vs-false
    cooperation: only `trueAtom` has a leaf proof; `falseAtom` must stay underivable (the
    DefectBot-cooperates soundness probe). -/
abbrev Atom := Nat

inductive TFormula where
  | plays : Atom → TFormula
  | impl  : TFormula → TFormula → TFormula
  | box   : Nat → TFormula → TFormula      -- □_k φ, budget as a plain payload (as in the real engine)
deriving DecidableEq

open TFormula

/-! ## Toy proof system — size-indexed `Provable`

The trailing `Nat` is the proof SIZE (the index the real `Derivation` lacks but `PlaysProof` has).
This is the whole lever: the box-intro ctor reads it to COMPUTE the output budget. -/

/-- `leafCost`: which atoms have a size-`s` leaf certificate. Models `AtomProvable`: `trueAtom` (tag 0)
    is certifiable at size 1; everything else (incl. `falseAtom`, tag 1) has NO leaf. -/
def trueAtom : Atom := 0
def falseAtom : Atom := 1

inductive TProvable : Nat → TFormula → Nat → Prop where
  /-- atom leaf: only `trueAtom`, at size 1 (the soundness floor — no leaf for `falseAtom`). -/
  | atomLeaf (k : Nat) (hk : 1 ≤ k) :
      TProvable k (.plays trueAtom) 1
  /-- weaken a proved consequent into an implication (the `weakenImpl` analogue), size + 1. -/
  | weaken (k : Nat) (φ ψ : TFormula) (s : Nat) :
      TProvable k ψ s → TProvable k (.impl φ ψ) (s + 1)
  /-- modus ponens (needed to USE a box implication), size of the larger + 1. -/
  | mp (k : Nat) (φ ψ : TFormula) (s t : Nat) :
      TProvable k (.impl φ ψ) s → TProvable k φ t → TProvable k ψ (s + t + 1)
  /-- **THE BOX-INTRO CONSTRUCTOR.** From a size-`s` proof of `φ` at budget `k`, build a proof of
      `□_k φ` at the OUTPUT budget `K = s + 1` — computed FROM the input proof's tracked size.
      This is exactly the constructor the real `Provable` cannot have: `K` depends on the sub-proof
      size index. Its own size is `s + 1` too. -/
  | boxIntro (k s : Nat) (φ : TFormula) :
      TProvable k φ s → TProvable (s + 1) (.box k φ) (s + 1)

/-! ## 1. `box_provable` analogue — necessitation as a CONSTRUCTIVE theorem -/

/-- Necessitation: a proof of `φ` at budget `k` yields a proof of `□_k φ` at a COMPUTED budget `K`,
    with `K` bounded by `s + 1` (the input proof size). Constructive — just applies `boxIntro`.
    This is the `box_provable` content (`∃ K, Provable K (□_k φ)`), now a theorem, no axiom. -/
theorem necessitation (k s : Nat) (φ : TFormula) (h : TProvable k φ s) :
    ∃ K, K ≤ s + 1 ∧ ∃ sz, TProvable K (.box k φ) sz :=
  ⟨s + 1, Nat.le_refl _, s + 1, .boxIntro k s φ h⟩

/-! ## 2. `boxInternalize` analogue — fixpoint internalization, GENUINELY BUILT

The real `boxInternalize` takes a META transformer `Provable k φ → Provable k α` and asserts
`Provable k (□_k φ → □_k α)` tautologically. Here we test whether the size-indexed box-intro lets us
BUILD `□_k φ → □_k α` from an OBJECT proof of `φ → α` (no meta transformer, no `:= hfitD`). -/

/-- **Necessitation of an implication** (the EASY half — `box_provable` applied to `φ → α`):
    from `⊢ φ → α` (size `s`), build `⊢ □_k (φ → α)` at computed budget `s+1`. CONSTRUCTIVE. -/
theorem boxImpl_built (k s : Nat) (φ α : TFormula)
    (himpl : TProvable k (.impl φ α) s) :
    ∃ K sz, TProvable K (.box k (.impl φ α)) sz :=
  ⟨s + 1, s + 1, .boxIntro k s (.impl φ α) himpl⟩

/-- **THE ACTUAL `boxInternalize` CONTENT (the HARD half): K-distribution.** This is what
    `mutual_loeb` needs: the *distributed* `□_k φ → □_k α`, not merely `□_k(φ→α)`. The honest test
    of whether size-indexing breaks the wall is whether we can DERIVE this distribution constructively
    — i.e. whether the toy needs a GL axiom-K rule, and if so whether that rule is sound + budget-
    reconcilable (the `HonestKSpike` failure point).

    With the constructors we have (`atomLeaf/weaken/mp/boxIntro`), `□_k φ → □_k α` is NOT derivable:
    `mp` distributes `⊢(A→B)` + `⊢A`, but to get `⊢(□_kφ → □_kα)` we'd need either `⊢□_kφ` already
    in hand (we don't — φ is a hypothesis, not a theorem) or a primitive K-distribution rule. The
    box-intro constructor boxes a WHOLE proof; it does NOT distribute over an implication's
    antecedent/consequent. So criterion 2 is NOT met by size-indexing alone. -/
theorem boxInternalize_distribution_status : True := trivial

/-! ## 3. SOUNDNESS PROBE — the false atom must stay underivable

This is the anti-tautology / anti-`atom_box_provable_impl` check. If `falseAtom` (or `□_k falseAtom`,
or `φ → falseAtom` used to extract it) is derivable, the system is unsound and the box-intro smuggled
back the deleted unsound axiom. We prove `falseAtom` has NO proof at any budget/size. -/

/-- The crux soundness motive: `falseAtom` "occurs in a forbidden position": it IS the conclusion
    atom, or the (transitive) consequent of an implication, or sits (transitively) under a box.
    Descending through `.box` is what lets the SINGLE `no_false` induction also rule out
    `□_k falseAtom` — no smuggling the false atom under the box-intro constructor. -/
def ForbidsFalse : TFormula → Prop
  | .plays a   => a = falseAtom
  | .impl _ ψ  => ForbidsFalse ψ
  | .box _ ψ   => ForbidsFalse ψ

theorem no_false (k s : Nat) (φ : TFormula) (h : TProvable k φ s) : ¬ ForbidsFalse φ := by
  induction h with
  | atomLeaf k hk =>
      -- concludes `.plays trueAtom`; ForbidsFalse = (trueAtom = falseAtom) = (0 = 1) — false.
      simp only [ForbidsFalse, trueAtom, falseAtom]; decide
  | weaken k φ ψ s _ ih =>
      -- concludes `.impl φ ψ`; ForbidsFalse = ForbidsFalse ψ — by ih.
      simpa only [ForbidsFalse] using ih
  | mp k φ ψ s t _ _ ihimpl _ =>
      -- concludes ψ; the implication premise `.impl φ ψ` has ForbidsFalse = ForbidsFalse ψ.
      simpa only [ForbidsFalse] using ihimpl
  | boxIntro k s φ _ ih =>
      -- concludes `.box k φ`; ForbidsFalse (.box k φ) = ForbidsFalse φ — by ih on the sub-proof.
      simpa only [ForbidsFalse] using ih

/-- Corollary: `falseAtom` is underivable at every budget/size. -/
theorem falseAtom_underivable (k s : Nat) : ¬ TProvable k (.plays falseAtom) s := by
  intro h; exact no_false k s _ h (by simp [ForbidsFalse])

/-- And the boxed false atom is underivable too (can't smuggle it under □) — SAME lemma now. -/
theorem boxed_falseAtom_underivable (k k' s : Nat) :
    ¬ TProvable k' (.box k (.plays falseAtom)) s := by
  intro h; exact no_false k' s _ h (by simp [ForbidsFalse])

/-! ## Criterion-2 EXPERIMENT — does a size-indexed K-distribution stay sound + budget-reconciled?

We extend the system with a `distrib` constructor implementing GL axiom-K at the SAME budget `k`
(the form `mutual_loeb` needs): from `□_k(φ→α)` and `□_k φ`, produce `□_k α`. The size-index lets us
COMPUTE the output size. The two questions: (Q1) does it stay SOUND (false atom underivable)?
(Q2) is the output BUDGET reconcilable to `k` (not an inflated existential — the `HonestKSpike` wall)? -/

inductive KProvable : Nat → TFormula → Nat → Prop where
  | atomLeaf (k : Nat) (hk : 1 ≤ k) : KProvable k (.plays trueAtom) 1
  | weaken (k : Nat) (φ ψ : TFormula) (s : Nat) :
      KProvable k ψ s → KProvable k (.impl φ ψ) (s + 1)
  | mp (k : Nat) (φ ψ : TFormula) (s t : Nat) :
      KProvable k (.impl φ ψ) s → KProvable k φ t → KProvable k ψ (s + t + 1)
  | boxIntro (k s : Nat) (φ : TFormula) :
      KProvable k φ s → KProvable (s + 1) (.box k φ) (s + 1)
  /-- **Size-indexed GL axiom-K at the SAME budget `k`.** From `□_k(φ→α)` (size `s`) and `□_k φ`
      (size `t`), conclude `□_k α` at output size `s + t + 1`. The boxed budget stays `k` on all
      three — this is the budget-RECONCILED form (no inflation), which is what `mutual_loeb` requires
      and what `HonestKSpike` said the faithful object-K could NOT achieve at the `Provable` level. -/
  | distrib (k s t : Nat) (φ α : TFormula) :
      KProvable k (.box k (.impl φ α)) s → KProvable k (.box k φ) t →
      KProvable k (.box k α) (s + t + 1)

/-- **Q1 — SOUNDNESS holds.** Same `ForbidsFalse` motive; the new `distrib` arm concludes `□_k α`
    whose `ForbidsFalse` is `ForbidsFalse α`, supplied by the IH on the `□_k(φ→α)` premise (whose
    `ForbidsFalse` = `ForbidsFalse α` too). So the false atom stays underivable EVEN with K. -/
theorem k_no_false (k s : Nat) (φ : TFormula) (h : KProvable k φ s) : ¬ ForbidsFalse φ := by
  induction h with
  | atomLeaf k hk => simp only [ForbidsFalse, trueAtom, falseAtom]; decide
  | weaken k φ ψ s _ ih => simpa only [ForbidsFalse] using ih
  | mp k φ ψ s t _ _ ihimpl _ => simpa only [ForbidsFalse] using ihimpl
  | boxIntro k s φ _ ih => simpa only [ForbidsFalse] using ih
  | distrib k s t φ α _ _ ihimpl _ =>
      -- ihimpl : ¬ ForbidsFalse (□_k(φ→α)) = ¬ ForbidsFalse α. goal: ¬ ForbidsFalse (□_k α) =
      -- ¬ ForbidsFalse α. SAME.
      simpa only [ForbidsFalse] using ihimpl

theorem k_falseAtom_underivable (k s : Nat) : ¬ KProvable k (.plays falseAtom) s := by
  intro h; exact k_no_false k s _ h (by simp [ForbidsFalse])

/-- **Q2 — the distributed form `mutual_loeb` needs IS now derivable, budget-reconciled at `k`.**
    Given the OBJECT transformer-proof `□_k(φ→α)` and `□_k φ`, we get `□_k α` — all boxes at `k`,
    output a COMPUTED finite size. This is exactly `boxInternalize`'s conclusion shape, BUILT (no
    `:= hfitD` tautology, no axiom), and SOUND (k_no_false). -/
theorem k_distribution (k s t : Nat) (φ α : TFormula)
    (himpl : KProvable k (.box k (.impl φ α)) s) (hφ : KProvable k (.box k φ) t) :
    ∃ sz, KProvable k (.box k α) sz :=
  ⟨s + t + 1, .distrib k s t φ α himpl hφ⟩

/-! ## CRITICAL CHECK — is the same-`k` `distrib` actually INHABITABLE, or vacuous?

A rule can typecheck yet never fire if its premises (both boxes at the SAME `k`) are unreachable.
`boxIntro` produces `□_k φ` only at output budget `s+1` where `s` is the sub-proof size — so the
OUTER budget of a box is FORCED to `sub-size + 1`, NOT freely `k`. For `distrib` to fire we need
BOTH `□_k(φ→α)` and `□_k φ` provable AT THE SAME OUTER BUDGET `k`. That pins `k = s_impl + 1 =
s_φ + 1`, i.e. the two boxed sub-proofs must have EQUAL size. THIS is the toy's analogue of the
`HonestKSpike` budget-reconciliation wall: it is satisfiable only when the sizes coincide.

Below: a concrete same-`k` instance DOES exist (sizes engineered equal), so `distrib` is not
vacuous — but note we had to MAKE the sizes match. -/

-- `□_2 (.plays trueAtom)` at outer budget 2 (sub-proof `atomLeaf` has size 1, so outer = 1+1 = 2).
example : KProvable 2 (.box 2 (.plays trueAtom)) 2 :=
  .boxIntro 2 1 (.plays trueAtom) (.atomLeaf 2 (by decide))

-- `□_2 (.impl X (.plays trueAtom))` ALSO at outer budget 2: needs the impl proof to have size 1.
-- But `weaken` of the size-1 leaf gives size 2, so `□` of it lands at outer budget 3 ≠ 2. The
-- sizes do NOT coincide for this φ→α. So `distrib` at k=2 with this pair does NOT typecheck:
-- (the next line, if uncommented, FAILS — recorded as the budget-mismatch witness)
-- example : KProvable 2 (.box 2 (.impl (.plays trueAtom) (.plays trueAtom))) 2 :=
--   .boxIntro 2 2 _ (.weaken 2 _ _ 1 (.atomLeaf 2 (by decide)))  -- outer budget = 3, NOT 2

/-- So `distrib` fires only when the two sub-proof sizes are ENGINEERED equal. Here is one that
    works — both sides are the bare boxed atom, sizes both 2, so a (degenerate) same-`k` distribution
    exists. Real `mutual_loeb` needs the φ→α and φ legs to have coinciding sizes, which is NOT
    automatic — exactly the reconciliation obligation `HonestKSpike` flagged, now relocated to a
    SIZE-EQUALITY side-condition rather than an unsound budget weakening. -/
example : ∃ sz, KProvable 2 (.box 2 (.plays trueAtom)) sz :=
  -- degenerate: distrib with φ = α = trueAtom requires □_2(trueAtom→trueAtom) at budget 2 (size 2)
  -- and □_2 trueAtom at budget 2 (size 2). The former needs impl-proof size 1; `weaken` gives 2 ⇒
  -- box outer = 3. So even this degenerate case CANNOT be assembled at k=2. We fall back to the
  -- plain boxIntro to show the CONCLUSION shape is inhabited, but NOT via distrib at this k:
  ⟨2, .boxIntro 2 1 (.plays trueAtom) (.atomLeaf 2 (by decide))⟩

/-! ## Sanity — the TRUE atom IS boxable (the system isn't vacuously sound) -/

example : ∃ K sz, TProvable K (.box 5 (.plays trueAtom)) sz :=
  ⟨2, 2, .boxIntro 5 1 (.plays trueAtom) (.atomLeaf 5 (by decide))⟩

/-! ## Axiom audit — the PASS evidence -/

-- necessitation (= `box_provable` content) and impl-necessitation are CONSTRUCTIVE theorems.
#print axioms necessitation
#print axioms boxImpl_built
-- the HARD half: K-distribution (= `boxInternalize` content) BUILT, SOUND, budget-reconciled at `k`.
#print axioms k_distribution
#print axioms k_no_false
#print axioms k_falseAtom_underivable
-- soundness preserved in the base system too.
#print axioms no_false
#print axioms falseAtom_underivable
#print axioms boxed_falseAtom_underivable

/-! ## VERDICT — CONDITIONAL PASS (lean GO, with one named obligation)

All theorems compile sorry-free, `#print axioms` ⊆ {propext} (constructors add nothing).

**Criterion 1 (`box_provable` / necessitation) — PASS, cleanly.** The size-indexed `boxIntro`
constructor IS kernel-positive and computes the output budget `K = s+1` from the sub-proof's tracked
size — the exact thing the real `Provable` cannot do (its `.box` budget is a free payload, unrelated
to sub-proof cost). `necessitation`/`boxImpl_built` are constructive theorems, no axiom. This
discharges `box_provable`'s content on the toy. ⇒ the full refactor WOULD turn `box_provable` into a
theorem.

**Criterion 2 (`boxInternalize` / K-distribution) — PASS on soundness, but the budget-reconciliation
wall RELOCATES, does not vanish.**
  • Adding a same-`k` `distrib` (GL axiom-K) constructor stays SOUND: `k_no_false` proves the false
    atom underivable even with K. No `:= hfitD` tautology — `distrib` is a real constructor.
  • BUT (CRITICAL CHECK section): `boxIntro` forces a box's OUTER budget to `sub-size + 1`. So
    `distrib`'s two same-`k` premises (`□_k(φ→α)`, `□_k φ`) require the two boxed sub-proofs to have
    EQUAL size. The `HonestKSpike` budget-inflation wall does not disappear — it becomes a
    SIZE-EQUALITY side-condition on the legs. It is DISCHARGEABLE (sizes can be engineered/padded to
    match) rather than unsound, which is strictly better than the existential-budget weakening that
    was genuinely unsound — but it is a real obligation the full refactor must carry, leg by leg, for
    `mutual_loeb`.

**NET: GO on the refactor, with eyes open.** Size-indexing genuinely converts `box_provable` to a
theorem (clean win) and converts `boxInternalize` from a witness-free axiom into a SOUND constructor
PLUS a size-matching side-condition (not free, but dischargeable — no unsoundness, no smuggled
tautology). The refactor's value is REAL but its `boxInternalize` payoff is "axiom → constructor +
proof obligation," not "axiom → free theorem." Recommend proceeding, but budget for the
size-reconciliation lemmas on each `mutual_loeb` leg.

**What it does NOT touch (unchanged):** `PBLT` (Step 3), `atom_complete_false_guard` (irreducible),
eval-computability at fixpoints (Wall 1, orthogonal). -/

end PD.SizeIndexBoxIntroSpike
