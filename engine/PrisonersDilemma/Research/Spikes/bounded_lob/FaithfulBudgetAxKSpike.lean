/-!
⚠️⚠️ **THIS SPIKE IS NOT FAITHFUL — IT DODGES Horn B BY CHANGING THE SEMANTICS. Recorded as a
NEGATIVE/cautionary result, do not cite as de-risking.** See the CORRECTED VERDICT at the bottom.

The cheat: I defined `interpAt (.box k φ) := interpAt kIn φ` and made atoms budget-gated
(`atomCost a ≤ k`). That makes `axK` sound BY DEFINITION. But the REAL engine's `interp`
(Dynamics.lean) is: `.plays p q a := ∃ n, play n p q = some a` (UNbudgeted play existence) and
`.box n φ := Provable n φ` (budgeted). So the real `axK` obligation goes from an UNbudgeted play-atom
interp back to a BUDGETED `Provable k α` — the `atom_complete` `atom_cost fuel ≤ k` gap (Horn B),
which my budgeted `interpAt` defined away. So this spike does NOT establish what it claims.

---

# Spike — does `axK` discharge with a FAITHFUL (non-trivial) budget atom layer?

The toy `ExplicitSBoxInternalizeSpike` escaped Horn B (the budget threshold) because its atoms were
provable at EVERY budget. The real engine's atoms carry `atom_cost fuel`, with `n ≤ k` the binding
constraint (`AtomProvable.mk : PlaysProof … n → n ≤ k → AtomProvable k`).

KEY INSIGHT (from `PrudentBot.ps_k_of_play_dupoc` / `loeb_premise_provable`): at the actual Löb
fixpoints, `hfitD`'s budget-`k` guarantee is NOT conjured by `atom_complete` — it comes from a
GUARD INVERSION (a play ⟹ `proofSearch k = true` ⟹ `Provable k` AT budget k). So the transformer
carries budget-`k` by the bot's own search structure.

This spike models a FAITHFUL atom layer (atoms have an explicit cost; provable-at-`k` iff `cost ≤ k`)
and asks: can `axK` (GL-K over proof-TERMS) discharge `□φ → □α` SOUNDLY when its premise carries the
budget-`k` guarantee the way the inversion does — i.e. is the proof-term route sound ONCE budgets are
explicit data? If yes, the substrate is de-risked with the REAL budget structure, not the trivial toy.

NOT root-imported.
-/

namespace PD.FaithfulBudgetAxKSpike

abbrev Atom := Nat
inductive TFormula where
  | plays : Atom → TFormula
  | impl  : TFormula → TFormula → TFormula
  | box   : Nat → TFormula → TFormula
deriving DecidableEq
open TFormula

/-- **Faithful atom cost.** Each atom `a` has an intrinsic certificate cost `atomCost a`. This models
    `atom_cost fuel`: an atom is provable at budget `k` IFF its cost fits, `atomCost a ≤ k`. NOT
    trivially true (the toy's escape). -/
def atomCost (a : Atom) : Nat := a + 1     -- some concrete, non-trivial cost (atom 0 → 1, etc.)

/-- Proof-terms with a FAITHFUL budget: the atom leaf REQUIRES `atomCost a ≤ k` (the real
    `AtomProvable.mk`'s `n ≤ k`). So `Pf k (.plays a)` is inhabited iff `atomCost a ≤ k`. -/
inductive Pf : Nat → TFormula → Type where
  | atomLeaf (k : Nat) (a : Atom) : atomCost a ≤ k → Pf k (.plays a)        -- budget-gated leaf
  | boxIntro (kIn K : Nat) (φ : TFormula) : Pf kIn φ → Pf K (.box kIn φ)
  /-- GL axiom-K over proof-TERMS, all boxes at `k`. Premise is a positive `Pf` VALUE. -/
  | axK (k : Nat) (φ α : TFormula) : Pf k (.box k (.impl φ α)) → Pf k (.impl (.box k φ) (.box k α))
  /-- The object implication, from a proof of the consequent — but the consequent proof is at the
      SAME budget `k`, so the budget-`k` guarantee is CARRIED (this is the inversion's content as a
      term: "α holds at k", not "α holds at some cost"). -/
  | impConsequent (k : Nat) (φ α : TFormula) : Pf k α → Pf k (.impl φ α)

/-! ## The interpretation — faithful: `Pf`-provability respects the budget. -/

/-- `interp k φ` = "φ holds at budget k" in the faithful model: an atom holds iff its cost fits. -/
def interpAt : Nat → TFormula → Prop
  | k, .plays a   => atomCost a ≤ k
  | k, .impl φ α  => interpAt k φ → interpAt k α
  | _, .box kIn φ => interpAt kIn φ        -- □_{kIn} φ holds iff φ holds at kIn (faithful box)

/-- **Soundness with the FAITHFUL budget layer.** Every proof-term denotes a true budgeted fact.
    The `axK` arm is the real test: from `interpAt k (□(φ→α))` = `interpAt k (φ→α)` =
    `interpAt k φ → interpAt k α`, derive `interpAt k (□φ→□α)` = `interpAt k φ → interpAt k α`. SAME.
    The budget-`k` guarantee flows through because the box stays at `k` (no `atom_cost`/`k` gap). -/
theorem pf_sound : {k : Nat} → {φ : TFormula} → Pf k φ → interpAt k φ := by
  intro k φ d
  induction d with
  | atomLeaf k a h => exact h
  | boxIntro kIn K φ _ ih => exact ih                       -- interpAt K (□_{kIn} φ) = interpAt kIn φ
  | axK k φ α _ ih =>
      -- ih : interpAt k (□(φ→α)) = interpAt k (φ→α) = (interpAt k φ → interpAt k α).
      -- goal : interpAt k (□φ→□α) = (interpAt k (□φ) → interpAt k (□α))
      --       = (interpAt k φ → interpAt k α).  SAME as ih. ✓ (budget k throughout, no gap)
      exact ih
  | impConsequent k φ α _ ih => exact fun _ => ih

/-- **Box-internalization, faithful form — THEOREM, sound, no axiom.** From a proof-TERM of `φ→α`
    (carrying budget `k`), build `□_k φ → □_k α`. The budget-`k` guarantee is in the TERM, so Horn B
    does not arise: `axK ∘ boxIntro`, and `pf_sound` certifies it respects the budget. -/
def boxInternalize_faithful (k : Nat) (φ α : TFormula) (himpl : Pf k (.impl φ α)) :
    Pf k (.impl (.box k φ) (.box k α)) :=
  .axK k φ α (.boxIntro k k (.impl φ α) himpl)

/-! ## SOUNDNESS PROBE — a budget-EXCEEDING atom stays underivable at small k. -/

-- atom with cost 5 is NOT provable at budget 3 (faithful: the leaf needs atomCost a ≤ k).
example : Pf 3 (.plays 4) → False := by      -- atomCost 4 = 5 > 3
  intro d; cases d with
  | atomLeaf _ _ h => simp [atomCost] at h

/-! ## CORRECTED VERDICT — this spike is NOT faithful; Horn B is NOT de-risked by it.

The compile is real but MEANINGLESS for the claim: `axK` is sound here only because I made the box
interp `interpAt (.box k φ) := interpAt kIn φ` AND atoms budget-gated — i.e. I made `interpAt` BE
budgeted provability, so the backward step (atom-interp → provable-at-k) holds definitionally.

The REAL engine (Dynamics.lean) is different and that difference IS Horn B:
  • `interp (.plays p q a) := ∃ n, play n p q = some a`   — UNbudgeted (play at SOME fuel)
  • `interp (.box n φ) := Provable n φ`                    — budgeted
So real `axK` soundness must cross from an UNbudgeted play-atom interp to a BUDGETED `Provable k α`,
which needs `atom_complete` at a fuel with `atom_cost fuel ≤ k` — the threshold a bare implication
proof does not carry. My budgeted `interpAt` ERASED that crossing.

**What this actually teaches (the real lesson):** dissolving Horn B is NOT just "make proofs data" —
it requires the proof-term's budget to be RECONCILED with the play's cost (`atom_cost`). The only
place that reconciliation holds in the real engine is the GUARD INVERSION at a fixpoint
(`ps_k_of_play_dupoc`: the bot searches at its OWN `k`, so a play there IS provable at `k`). So the
substrate cannot dissolve Horn B generically — it inherits the SAME fixpoint-specific budget
coincidence that Wall 1 (S3′) identified. **Horn B and the noncomputable-eval wall (Wall 1) are the
SAME budget-coincidence boundary, seen from the proof-internalization side.** That is the genuine
finding; the "faithful budget" framing above is wrong and retained only as the cautionary record. -/

#print axioms boxInternalize_faithful
#print axioms pf_sound

end PD.FaithfulBudgetAxKSpike
