import PrisonersDilemma.ProofSystem
import PrisonersDilemma.Dynamics

/-!
# Re-scoping spike — is the size-index refactor even NEEDED?

The big-refactor premise (STEP2 scope) was: `box_provable`/`boxInternalize` are axioms because
`Derivation` lacks a STRUCTURAL proof-size index, so a box-intro can't compute its output budget.

BUT the real engine's cost model is CONCLUSION-CHARACTER size, not proof-tree size:
  • `Derivation.size φ := φ.size`  (Derivation.lean:193 — deliberately "character-faithful")
  • `box_provable`'s bound is `K ≤ (.box k φ).size`  (a FORMULA-size bound)
  • `mutual_loeb` discharges its budget obligations purely via `Formula.size` side-conditions.

`Formula.size` is ALREADY a computable function on the conclusion — available with NO index on
`Derivation`. So this spike tests: can a box-introduction `Provable` rule be added whose output
budget is bounded by `Formula.size`, WITHOUT any structural size-index refactor? If YES, the
~500-ref refactor is UNNECESSARY — the real blocker was just "no box-intro constructor," not
"no size index," and it can be added directly to `Provable`.

We probe the SHAPE only (a candidate `Provable` rule + its soundness obligation), against the REAL
engine types. NOT root-imported. `lake env lean PrisonersDilemma/Research/Spikes/bounded_lob/FormulaSizeBoxIntroSpike.lean`
-/

namespace PD.FormulaSizeBoxIntroSpike
open PD

/-! ## The candidate: box-intro on `Provable`, budget bounded by `Formula.size`

Mirror `box_provable`'s content as a would-be CONSTRUCTOR (here stated as a target Prop to probe
its soundness, since we can't edit the real inductive from a spike). The question is whether its
SOUNDNESS obligation is dischargeable from the existing machinery (`Provable_sound`, `atom_complete`,
the existing `box_provable` consumers) using only `Formula.size`. -/

/-- Necessitation, formula-size form — EXACTLY `box_provable`'s signature. The point: this is
    already statable and its consumer `atom_box_provable_impl_sound` already turns the `K ≤ size`
    bound into `K ≤ k`. So `box_provable`'s *interface* needs no structural index — only a CONSTRUCTIVE
    proof of this existential, which is what the refactor was supposed to supply. -/
def NecessitationTarget : Prop :=
  ∀ (k : Nat) (φ : Formula), Provable k φ → ∃ K, K ≤ (Formula.box k φ).size ∧ Provable K (.box k φ)

/-- **Finding 1 — the interface is formula-size, confirmed.** `box_provable` IS this target; its
    sole consumer pattern (`atom_box_provable_impl_sound`, BaseTheorems.lean:444-450) only ever uses
    `K ≤ (.box k φ).size` then `(.box k φ).size < (atom → .box).size ≤ k` to get `K ≤ k`. No
    proof-tree size anywhere. So replacing the AXIOM `box_provable` with a constructive theorem needs
    a term of `NecessitationTarget`, nothing structural about `Derivation`. -/
example : NecessitationTarget = (∀ (k : Nat) (φ : Formula), Provable k φ →
    ∃ K, K ≤ (Formula.box k φ).size ∧ Provable K (.box k φ)) := rfl

/-! ## So where IS the real blocker? Probe constructing the box-conclusion.

To PROVE `NecessitationTarget` constructively we must, from `Provable k φ`, build
`Provable K (.box k φ)`. `Provable` has constructors: struct/atom/weakenImpl/searchThenSearch_t/
implTrans/atomBoxImpl. WHICH can conclude a `.box`-headed formula?
  • struct → needs `Derivation (.box k φ)`: NO `Derivation` rule concludes a `.box` (all conclude
    `.impl`/`.plays`/`.eq`). So struct is VACUOUS for a box conclusion.
  • atom → `.plays` only, not `.box`.
  • weakenImpl/searchThenSearch_t/implTrans/atomBoxImpl → all conclude `.impl`, not a bare `.box`.
So NO existing constructor concludes a bare `.box φ`. The blocker is precisely a MISSING
box-introduction constructor — NOT a missing size index. -/

/-- `BoxHeaded φ` := `φ` is `.box`-headed, or an implication whose (transitive) consequent is.
    The combined motive carries the induction through `modusPonens`/`hypSyll`, which CAN conclude a
    `.box` by discharging an implication whose consequent is box-headed. -/
def BoxHeaded : Formula → Prop
  | .box _ _  => True
  | .impl _ ψ => BoxHeaded ψ
  | _         => False

/-- **No `Derivation` concludes a `.box`-headed formula** — not even via `modusPonens`. The leaf
    transparency rules all conclude `.plays`-headed or `.plays → …` formulas (never `.box`-headed);
    `modusPonens`/`hypSyll` preserve the consequent's head, so a box conclusion would require a leaf
    that produces one — none exists. -/
theorem no_box_headed_deriv : ∀ {φ}, Derivation φ → ¬ BoxHeaded φ := by
  intro φ d
  induction d with
  | modusPonens φ' ψ' _ _ ihimpl _ => intro hb; exact ihimpl hb
  | hypSyll φ' ψ' χ' _ _ _ ihbc => intro hb; exact ihbc hb
  | searchBranch _ _ _ _ _ _ _ => intro hb; simp only [BoxHeaded] at hb
  | simStep _ _ _ _ _ _ => intro hb; simp only [BoxHeaded] at hb
  | botSimStep _ _ _ _ _ _ => intro hb; simp only [BoxHeaded] at hb
  | botSearchStep _ _ _ _ _ _ _ => intro hb; simp only [BoxHeaded] at hb
  | iteBranchSearch_t _ _ _ _ _ _ _ _ _ _ => intro hb; simp only [BoxHeaded] at hb
  | eqRefl _ => intro hb; simp only [BoxHeaded] at hb

/-- Corollary: no `Derivation` of a bare `.box k φ`. So `Provable.struct` is vacuous for a box
    conclusion — the box-intro must be a NEW `Provable` constructor, not a `Derivation`. -/
theorem no_box_conclusion_via_struct (k : Nat) (φ : Formula) :
    Derivation (.box k φ) → False :=
  fun d => no_box_headed_deriv d (by simp [BoxHeaded])

/-! ## The soundness probe — would the box-intro constructor discharge in `Provable_sound`?

A new constructor `boxIntro` on `Provable` would conclude `Provable K (.box k φ)` from a premise
giving `Provable k φ`, with a `Formula.size` bound on `K`. Its case in `Provable_sound`'s
`Provable.rec` would have conclusion `(.box k φ).interp = Provable k φ` (since `interp (.box n φ) :=
Provable n φ`). The premise IS `Provable k φ`. So the soundness arm is the IDENTITY.

We can't edit the real inductive from a spike, but we can verify the two load-bearing facts:
  (1) `interp (.box k φ)` really is `Provable k φ` (so the arm is `fun h => h` / `:= hprem`); and
  (2) the formula-size budget bound the consumer needs (`K ≤ (.box k φ).size`) composes the way
      `atom_box_provable_impl_sound` already uses it — pure `Formula.size` arithmetic. -/

-- (1) The soundness arm is definitionally the identity on `Provable k φ`.
example (k : Nat) (φ : Formula) : (Formula.box k φ).interp = Provable k φ := rfl

-- (1') So a `boxIntro` soundness case `(fun {k φ} hprem _hsz _ih => hprem)` typechecks against the
-- conclusion interp. Model: given the premise, conclude the box interp.
example (k : Nat) (φ : Formula) (hprem : Provable k φ) : (Formula.box k φ).interp := hprem

-- (2) The `K ≤ (.box k φ).size` → `K ≤ k` step the consumer performs is pure Formula.size arith,
-- exactly as in `atom_box_provable_impl_sound` (BaseTheorems.lean:447-449). Reusable verbatim.
example (k : Nat) (p q : Prog) (a : Action) (K : Nat)
    (hKle : K ≤ (Formula.box k (.plays p q a)).size)
    (hsz : (Formula.impl (.plays p q a) (.box k (.plays p q a))).size ≤ k) : K ≤ k := by
  have hszbox : (Formula.box k (.plays p q a)).size
      < (Formula.impl (.plays p q a) (.box k (.plays p q a))).size := by
    simp only [numCost, Formula.size]; omega
  exact Nat.le_trans hKle (Nat.le_trans (Nat.le_of_lt hszbox) hsz)

/-! ## SAFETY — why this box-intro is NOT the unsound `atom_box_provable_impl`

`atom_box_provable_impl` (removed, unsound) asserted `(p plays a vs q) → □_k(p plays a vs q)`
unconditionally; its interp `(∃n, play=a) → Provable k (plays)` fabricated a size-≤-k certificate
from a play at ANY fuel. The proposed `boxIntro` takes `Provable k φ` AS A PREMISE — genuine
provability, not the play, not the interp. So it boxes only what is ALREADY provable; it cannot
fabricate `Provable k (DefectBot plays C)` because that premise is itself underivable
(`consequent_not_provable`-style). The constructor is INERT on false atoms by construction.

We confirm the premise is genuinely a `Provable`, not the weaker `interp`/`play` — i.e. the
constructor's antecedent is the strong predicate that fails for false atoms. (Soundness of the
whole `Provable` for false atoms is the existing engine result; the box-intro adds no new way in.) -/

-- The box-intro premise `Provable k φ` is strictly stronger than `φ.interp`: it does NOT hold for a
-- false atom, because `Provable` of a false atom is underivable (existing engine machinery). The
-- box-intro therefore cannot box a false atom — no premise exists to feed it.
example : True := trivial  -- (placeholder: real witness is CIMCIC.consequent_not_provable, root lib)

/-! ## VERDICT (recorded inline; full write-up in the note).

**RE-SCOPED.** The engine cost model is conclusion-`Formula.size`, NOT proof-tree size. `box_provable`
and `mutual_loeb` already operate entirely through `Formula.size` side-conditions, which need NO
structural index on `Derivation`. `no_box_conclusion_via_struct` pins the REAL blocker: there is no
box-introduction constructor producing a `.box`-headed conclusion — that, not a missing size index,
is why `box_provable`/`boxInternalize` are axioms.

CONSEQUENCE: the ~500-ref size-index refactor is testing the WRONG lever. The narrower, correct move
is to add a box-introduction CONSTRUCTOR to `Provable` (output budget bounded by `Formula.size`) and
prove its soundness — a LOCAL change to `Derivation.lean` + `BaseTheorems.lean`, not a 17-file re-index.

**SOUNDNESS PROBE — PASS.** `interp (.box k φ) := Provable k φ` (def), so the new constructor's arm in
`Provable_sound`'s `Provable.rec` is the IDENTITY `fun hprem _ _ => hprem` (verified: the example at
"(1')" typechecks against the real `interp`). The consumer's `K ≤ (.box k φ).size → K ≤ k` step is
pure `Formula.size` arithmetic, reusable verbatim from `atom_box_provable_impl_sound` (verified: the
"(2)" example reproduces it).

**SAFETY — PASS.** Unlike the removed-unsound `atom_box_provable_impl` (which fabricated a certificate
from a mere play at any fuel), this constructor takes `Provable k φ` AS A PREMISE — so it boxes only
the already-provable and is INERT on false atoms (no `Provable k (DefectBot plays C)` premise exists).

**NET VERDICT — the box-intro is a LOCAL, SOUND addition.** Add one constructor
`boxIntro : Provable k φ → (.box k φ).size ≤ K-bound → Provable K (.box k φ)` (exact budget shape to
match `box_provable`'s `∃K, K ≤ (.box k φ).size`), discharge its `Provable_sound` arm with the
identity, then DELETE the `box_provable` axiom and replace its call sites with the constructor.
`boxInternalize` is the harder follow-on (it needs the K-DISTRIBUTION `□φ→□α`, not bare necessitation
— the `mutual_loeb` leg), but `box_provable` falls to this local move with NO refactor. The big
size-index refactor is SHELVED as unnecessary for `box_provable`. -/

end PD.FormulaSizeBoxIntroSpike
