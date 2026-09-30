import ArithS.Cells.Common.Templates
import ArithS.Assembly.Uniform

/-!
# ArithS.Cells.Common.Families — the two-guard family `pQ`, its Löb premise, the ∧-elimination slack

Consolidation stage 5 (`Research/Notes/ROUTE_B_CELLS_MAP.md`, 2026-09-24).

1. **The family `pQ q := q ⋏ τq`** and its lemmas (`instB_quote_pQ`, `formulaLen_instB_pQ`, `pQ_both_V`,
   `eval_pQ_std`, `eval_pQ_swap`), MOVED unchanged from `Cells/FlipCells`. Every per-cell family
   (`pConj`, `pDM`, `pBD`, `pJM`, `pCD`, …) is `pQ` of its guard by definition.
2. **`loebSound_pQ_of`** (NEW): the Löb premise of `pQ q` at slack `(7, 8)` from ONE semantic fact — both
   instances found within `k` make `q(k)` and `τq(k)` true in the standard reading. `loebSound_pWM`/
   `loebSound_pWW` (`Cells/FlipCells`) are its corollaries.
3. **`slack_depth_le`** (NEW): the ∧-elimination slack at depth `d` — `d` elimination steps on pairs of
   conjunct lengths bounded by the total `z` cost at most `7 d + 8 d z`; `slack4_le`/`slack4_le'`
   (`Cells/DIMCID`, `(14, 16)`) and `slack6_le₁`/`slack6_le`/`slack6_le'` (`Cells/JustSlot`, `(21, 24)`)
   are its corollaries, the ℕ forms `slack4_nat*`/`slack6_nat*` corollaries of those through `le_def`.
   (`pConj_slack_nat`, `Assembly/Cell`, is upstream of this module and untouched.)
4. `nat_le_of_le_def` (MOVED from `Cells/FlipCells`), the companion of `Assembly/Family.le_def_trans`.

`loebSound_pG_of`/`loebSound_pG_of_above` moved into `Cells/DIMCID` (right after `pG`'s conjunction
section — they need `pG`), where `describes_dimcid`/`describes_mirror` make `loebSound_pDD`/`_pDMi`
corollaries (`describes_CB` in `Common/Templates` does the same for `loebSound_pDi0`).
-/

namespace ArithS

open FFL FFL.FirstOrder Arithmetic Bootstrapping
open PeanoMinus ISigma0 ISigma1
open FFL.FirstOrder.Arithmetic.Bootstrapping.Arithmetic
open LAct

variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

/-! ### 1. ℕ/`V` bridging -/

section bridging

/-- Foundation's `≤` at ℕ (`le_def`) read as `Nat.le`, with the sides inferred (never restate a term that
carries `‖k‖ ^ d`: the pow instance at ℕ is `instCommSemiring_foundation`'s, not `Nat.instMonoid`'s). -/
lemma nat_le_of_le_def {a b : ℕ} (h : a = b ∨ a < b) : a ≤ b := by omega

end bridging

/-! ### 2. The two-guard family `pQ q := q ⋏ τq` -/

section pQ

/-- **The two-guard family of a single searcher's cell**: its guard's fixed formula `q` AND the transposed
searcher's `τq` — one box, ∧-elimination on codes, the same slack `(7, 8)` as `pConj`. -/
noncomputable def pQ (q : Semisentence LAct 1) : Semisentence LAct 1 := q ⋏ Semiformula.lMap swap q

lemma pQ_def (q : Semisentence LAct 1) : pQ q = q ⋏ Semiformula.lMap swap q := rfl

lemma lMap_swap_pQ (q : Semisentence LAct 1) :
    Semiformula.lMap swap (pQ q) = Semiformula.lMap swap q ⋏ q := by
  rw [pQ_def, LogicalConnective.HomClass.map_and, lMap_swap_swap]

theorem instB_quote_pQ (q : Semisentence LAct 1) (k : V) :
    instB (⌜pQ q⌝ : V) k = instB (⌜q⌝ : V) k ^⋏ instB (⌜Semiformula.lMap swap q⌝ : V) k :=
  instB_quote_and _ _ k

lemma formulaLen_instB_pQ (q : Semisentence LAct 1) (k : V) :
    formulaLen LAct (instB (⌜pQ q⌝ : V) k) =
      formulaLen LAct (instB (⌜q⌝ : V) k) + formulaLen LAct (instB (⌜Semiformula.lMap swap q⌝ : V) k) + 1 := by
  rw [instB_quote_pQ,
    formulaLen_and (isFormula_instB_quote _ k).isUFormula (isFormula_instB_quote _ k).isUFormula]

/-- **Both instances are provable within `k` from a box of the family with the slack** (∧-elimination on
codes, `pG_guards_V`'s shape for an arbitrary `q`). -/
theorem pQ_both_V (q : Semisentence LAct 1) (k a : V)
    (ha : a + 8 * (formulaLen LAct (instB (⌜q⌝ : V) k) + formulaLen LAct (instB (⌜Semiformula.lMap swap q⌝ : V) k))
      + 7 ≤ k)
    (h : LenBoxUnbounded TAct a (instB (⌜pQ q⌝ : V) k)) :
    LenBox TAct k (instB (⌜q⌝ : V) k) ∧ LenBox TAct k (instB (⌜Semiformula.lMap swap q⌝ : V) k) := by
  rw [instB_quote_pQ] at h
  have hx := isFormula_instB_quote q k
  have hy := isFormula_instB_quote (Semiformula.lMap swap q) k
  exact ⟨(lenBoxUnbounded_iff_lenBox _ _).mp (lenBoxUnbounded_mono_V ha (lenBoxUnbounded_andL_V hx hy h)),
    (lenBoxUnbounded_iff_lenBox _ _).mp (lenBoxUnbounded_mono_V ha (lenBoxUnbounded_andR_V hx hy h))⟩

omit [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁] in
/-- `pQ q (k)` in the standard reading: both conjuncts. -/
theorem eval_pQ_std (q : Semisentence LAct 1) (k : V) :
    Semiformula.Eval (s := stdReading V) ![k] Empty.elim (pQ q) ↔
      Semiformula.Eval (s := stdReading V) ![k] Empty.elim q ∧
      Semiformula.Eval (s := stdReading V) ![k] Empty.elim (Semiformula.lMap swap q) := by
  rw [pQ_def]
  simp only [LogicalConnective.HomClass.map_and, LogicalConnective.Prop.and_eq]

omit [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁] in
/-- `pQ q (k)` in the swapped reading: the conjuncts exchange roles. -/
theorem eval_pQ_swap (q : Semisentence LAct 1) (k : V) :
    Semiformula.Eval (s := swappedReading V) ![k] Empty.elim (pQ q) ↔
      Semiformula.Eval (s := stdReading V) ![k] Empty.elim (Semiformula.lMap swap q) ∧
      Semiformula.Eval (s := stdReading V) ![k] Empty.elim q := by
  rw [eval_swappedReading, lMap_swap_pQ]
  simp only [LogicalConnective.HomClass.map_and, LogicalConnective.Prop.and_eq]

/-- **The Löb premise of `pQ q` at slack `(7, 8)`, from one semantic fact**: whenever both instances `q(k)`
and `τq(k)` are provable within `k`, both are TRUE in the standard reading. The box of the family yields
the two instances by ∧-elimination on codes (`pQ_both_V`); the two readings of `pQ q` are the two
conjunction orders (`eval_pQ_std`, `eval_pQ_swap`). -/
theorem loebSound_pQ_of (q : Semisentence LAct 1)
    (h : ∀ (V : Type) [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁] (k : V),
      LenBox TAct k (instB (⌜q⌝ : V) k) → LenBox TAct k (instB (⌜Semiformula.lMap swap q⌝ : V) k) →
      Semiformula.Eval (s := stdReading V) ![k] Empty.elim q ∧
      Semiformula.Eval (s := stdReading V) ![k] Empty.elim (Semiformula.lMap swap q)) :
    LoebSound (pQ q) 7 8 := by
  intro V _ _ k a ha hp
  have : V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁ := inferInstance
  have ha' : a + 8 * (formulaLen LAct (instB (⌜q⌝ : V) k) +
      formulaLen LAct (instB (⌜Semiformula.lMap swap q⌝ : V) k)) + 7 ≤ k :=
    le_trans (pConj_slack_le a _ _ _ (formulaLen_instB_pQ q k)) ha
  obtain ⟨h1, h2⟩ := pQ_both_V q k a ha' hp
  obtain ⟨hA, hB⟩ := h V k h1 h2
  exact ⟨(eval_pQ_std q k).mpr ⟨hA, hB⟩, (eval_pQ_swap q k).mpr ⟨hB, hA⟩⟩

end pQ

/-! ### 3. The ∧-elimination slack at depth `d` -/

section slack

/-- **The ∧-elimination slack at depth `d`**: `d` elimination steps, the `i`-th on a pair of conjunct
lengths `(xᵢ, yᵢ)` with `xᵢ + yᵢ ≤ z` (`z` the length of the whole family instance), cost
`Σᵢ (8 (xᵢ + yᵢ) + 7) ≤ 7 d + 8 d z` beyond the proof length `a` — the family slack `(7 d, 8 d)`:
`(7, 8)` at depth 1 (`pConj_slack_le`), `(14, 16)` at depth 2 (`slack4_le`), `(21, 24)` at depth 3
(`slack6_le`). -/
theorem slack_depth_le (a z : V) :
    ∀ l : List (V × V), (∀ p ∈ l, p.1 + p.2 ≤ z) →
      a + (l.map fun p ↦ 8 * (p.1 + p.2) + 7).sum ≤ a + (7 * (l.length : V) + 8 * (l.length : V) * z)
  | [], _ => by simp
  | p :: l, h => by
    have hp : p.1 + p.2 ≤ z := h p (by simp)
    have ih := slack_depth_le a z l fun q hq ↦ h q (by simp [hq])
    rw [List.map_cons, List.sum_cons, List.length_cons, Nat.cast_succ]
    calc a + (8 * (p.1 + p.2) + 7 + (l.map fun p ↦ 8 * (p.1 + p.2) + 7).sum)
        = a + (l.map fun p ↦ 8 * (p.1 + p.2) + 7).sum + (8 * (p.1 + p.2) + 7) := by ring
      _ ≤ a + (7 * (l.length : V) + 8 * (l.length : V) * z) + (8 * z + 7) := by gcongr
      _ = a + (7 * ((l.length : V) + 1) + 8 * ((l.length : V) + 1) * z) := by ring

end slack

end ArithS
