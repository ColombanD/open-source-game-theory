import ArithS.Necessitation.Lib.Basic

/-!
# ArithS.Necessitation.Lib.Sets — the `sets` rows of the library `Λ`

`DESIGN_inner_necessitation.md` §3.1, rows `sets` and the set-shaped `totality` entries: facts
about sequents as HFS bit-sets (`insert`, `⊆`, `∅`), `IsFormulaSet`, `setShift` and the
totality of `insert`/`setShift`/`shift`/`free` — each an `ℒₒᵣ`-sentence in PRENEX universal
form over the SAME Σ₁/Δ₁ formula objects the target uses (`!insertDef`, `!bitSubsetDef`,
`!(isFormulaSet LAct).sigma/.pi`, `!(setShiftGraph LAct)`, `!(shiftGraph LAct)`,
`!(freeGraph LAct)`), true in every model of `𝗜𝚺₁`, hence a `𝗣𝗔`-theorem (`complete`) and a
library sentence (`Lib`, a `TAct`-proof of fixed standard length in every model).

**Convention.** Each row is a BODY `xB : ArithmeticSemisentence m` written `“x₀ … x_{m-1}. B”`
(index order: `x₀ = #0` is bound by the INNERMOST quantifier) and the sentence `x := ∀¹* xB`,
so that `Lib.univ_code lib_x` yields a proof code of `qqAlls ⌜xB⌝ m` (`quote_alls`). The
`models_x` lemma lists the variables in index order.

Hypotheses of Δ₁ predicates are taken in `.pi` form and conclusions in `.sigma` form (the
`cutSentence` convention); the four properness bridges (`isFormulaSetSigmaPi`, …) convert.
-/

namespace ArithS

open FFL FFL.FirstOrder Arithmetic Bootstrapping
open PeanoMinus ISigma0 ISigma1
open LAct

variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

/-! ### Membership and `insert` -/

/-- `x ∈ s → x ∈ insert y s`. -/
noncomputable def memInsertOfMemB : ArithmeticSemisentence 4 :=
  “t y s x. x ∈ s → !insertDef t y s → x ∈ t”
noncomputable def memInsertOfMem : ArithmeticSentence := ∀¹* memInsertOfMemB

lemma models_memInsertOfMem :
    V↓[ℒₒᵣ] ⊧ memInsertOfMem ↔ ∀ t y s x : V, x ∈ s → t = insert y s → x ∈ t := by
  simp [memInsertOfMem, memInsertOfMemB, models_iff, Matrix.vecForall_iff]

theorem pa_proves_memInsertOfMem : 𝗣𝗔 ⊢ memInsertOfMem :=
  Lib.pa_proves_of_models fun _ _ _ ↦ models_memInsertOfMem.mpr fun _ _ _ _ hx h ↦ by
    subst h; simp [hx]

theorem lib_memInsertOfMem : Lib memInsertOfMem := Lib.of_pa pa_proves_memInsertOfMem

/-- `s ⊆ t → x ∈ t → insert x s ⊆ t`. -/
noncomputable def insertSubsetB : ArithmeticSemisentence 4 :=
  “u x t s. !bitSubsetDef s t → x ∈ t → !insertDef u x s → !bitSubsetDef u t”
noncomputable def insertSubset : ArithmeticSentence := ∀¹* insertSubsetB

lemma models_insertSubset :
    V↓[ℒₒᵣ] ⊧ insertSubset ↔ ∀ u x t s : V, s ⊆ t → x ∈ t → u = insert x s → u ⊆ t := by
  simp [insertSubset, insertSubsetB, models_iff, Matrix.vecForall_iff]

theorem pa_proves_insertSubset : 𝗣𝗔 ⊢ insertSubset :=
  Lib.pa_proves_of_models fun _ _ _ ↦ models_insertSubset.mpr fun _ _ _ _ hst hx h ↦ by
    subst h
    intro z hz
    rcases mem_bitInsert_iff.mp hz with rfl | hz
    · exact hx
    · exact hst hz

theorem lib_insertSubset : Lib insertSubset := Lib.of_pa pa_proves_insertSubset

/-- `x ∈ s → insert x s = s`. -/
noncomputable def insertEqOfMemB : ArithmeticSemisentence 3 :=
  “t s x. x ∈ s → !insertDef t x s → t = s”
noncomputable def insertEqOfMem : ArithmeticSentence := ∀¹* insertEqOfMemB

lemma models_insertEqOfMem :
    V↓[ℒₒᵣ] ⊧ insertEqOfMem ↔ ∀ t s x : V, x ∈ s → t = insert x s → t = s := by
  simp [insertEqOfMem, insertEqOfMemB, models_iff, Matrix.vecForall_iff]

theorem pa_proves_insertEqOfMem : 𝗣𝗔 ⊢ insertEqOfMem :=
  Lib.pa_proves_of_models fun _ _ _ ↦ models_insertEqOfMem.mpr fun _ _ _ hx h ↦ by
    subst h; exact insert_eq_self_of_mem hx

theorem lib_insertEqOfMem : Lib insertEqOfMem := Lib.of_pa pa_proves_insertEqOfMem

/-! ### `IsFormulaSet` -/

/-- `IsFormulaSet s → IsFormula p → IsFormulaSet (insert p s)`. -/
noncomputable def isFormulaSetInsertB : ArithmeticSemisentence 3 :=
  “t p s. !(isFormulaSet LAct).pi s → !(isSemiformula LAct).pi 0 p → !insertDef t p s →
    !(isFormulaSet LAct).sigma t”
noncomputable def isFormulaSetInsert : ArithmeticSentence := ∀¹* isFormulaSetInsertB

lemma models_isFormulaSetInsert :
    V↓[ℒₒᵣ] ⊧ isFormulaSetInsert ↔
    ∀ t p s : V, IsFormulaSet LAct s → IsFormula LAct p → t = insert p s → IsFormulaSet LAct t := by
  simp [isFormulaSetInsert, isFormulaSetInsertB, models_iff, Matrix.vecForall_iff]

theorem pa_proves_isFormulaSetInsert : 𝗣𝗔 ⊢ isFormulaSetInsert :=
  Lib.pa_proves_of_models fun _ _ _ ↦ models_isFormulaSetInsert.mpr fun _ _ _ hs hp h ↦ by
    subst h; exact IsFormulaSet.insert_iff.mpr ⟨hp, hs⟩

theorem lib_isFormulaSetInsert : Lib isFormulaSetInsert := Lib.of_pa pa_proves_isFormulaSetInsert

/-! ### Properness bridges (`.sigma ↔ .pi`) -/

noncomputable def isSemiformulaSigmaPiB : ArithmeticSemisentence 2 :=
  “p n. !(isSemiformula LAct).sigma n p → !(isSemiformula LAct).pi n p”
noncomputable def isSemiformulaSigmaPi : ArithmeticSentence := ∀¹* isSemiformulaSigmaPiB

lemma models_isSemiformulaSigmaPi :
    V↓[ℒₒᵣ] ⊧ isSemiformulaSigmaPi ↔
    ∀ p n : V, IsSemiformula LAct n p → IsSemiformula LAct n p := by
  simp [isSemiformulaSigmaPi, isSemiformulaSigmaPiB, models_iff, Matrix.vecForall_iff]

theorem pa_proves_isSemiformulaSigmaPi : 𝗣𝗔 ⊢ isSemiformulaSigmaPi :=
  Lib.pa_proves_of_models fun _ _ _ ↦ models_isSemiformulaSigmaPi.mpr fun _ _ h ↦ h

theorem lib_isSemiformulaSigmaPi : Lib isSemiformulaSigmaPi :=
  Lib.of_pa pa_proves_isSemiformulaSigmaPi

/-! ### `setShift` -/

/-- `x ∈ s → shift x ∈ setShift s`. -/
noncomputable def shiftMemSetShiftB : ArithmeticSemisentence 4 :=
  “y t x s. x ∈ s → !(setShiftGraph LAct) t s → !(shiftGraph LAct) y x → y ∈ t”
noncomputable def shiftMemSetShift : ArithmeticSentence := ∀¹* shiftMemSetShiftB

lemma models_shiftMemSetShift :
    V↓[ℒₒᵣ] ⊧ shiftMemSetShift ↔
    ∀ y t x s : V, x ∈ s → t = setShift LAct s → y = shift LAct x → y ∈ t := by
  simp [shiftMemSetShift, shiftMemSetShiftB, models_iff, Matrix.vecForall_iff,
    setShift.defined.iff, shift.defined.iff]

theorem pa_proves_shiftMemSetShift : 𝗣𝗔 ⊢ shiftMemSetShift :=
  Lib.pa_proves_of_models fun _ _ _ ↦ models_shiftMemSetShift.mpr fun _ _ _ _ hx ht hy ↦ by
    subst ht; subst hy; exact shift_mem_setShift hx

theorem lib_shiftMemSetShift : Lib shiftMemSetShift := Lib.of_pa pa_proves_shiftMemSetShift

/-- `y ∈ setShift s → ∃ x ∈ s, y = shift x`. -/
noncomputable def memSetShiftInvB : ArithmeticSemisentence 3 :=
  “y t s. !(setShiftGraph LAct) t s → y ∈ t → ∃ x, x ∈ s ∧ !(shiftGraph LAct) y x”
noncomputable def memSetShiftInv : ArithmeticSentence := ∀¹* memSetShiftInvB

lemma models_memSetShiftInv :
    V↓[ℒₒᵣ] ⊧ memSetShiftInv ↔
    ∀ y t s : V, t = setShift LAct s → y ∈ t → ∃ x, x ∈ s ∧ y = shift LAct x := by
  simp [memSetShiftInv, memSetShiftInvB, models_iff, Matrix.vecForall_iff,
    setShift.defined.iff, shift.defined.iff]

theorem pa_proves_memSetShiftInv : 𝗣𝗔 ⊢ memSetShiftInv :=
  Lib.pa_proves_of_models fun _ _ _ ↦ models_memSetShiftInv.mpr fun _ _ _ ht hy ↦ by
    subst ht
    obtain ⟨x, hx, rfl⟩ := mem_setShift_iff.mp hy
    exact ⟨x, hx, rfl⟩

theorem lib_memSetShiftInv : Lib memSetShiftInv := Lib.of_pa pa_proves_memSetShiftInv

/-! ### Totality -/

/-- `∀ s, ∃ t, t = setShift s`. -/
noncomputable def setShiftTotalB : ArithmeticSemisentence 1 := “s. ∃ t, !(setShiftGraph LAct) t s”
noncomputable def setShiftTotal : ArithmeticSentence := ∀¹* setShiftTotalB

lemma models_setShiftTotal : V↓[ℒₒᵣ] ⊧ setShiftTotal ↔ ∀ s : V, ∃ t, t = setShift LAct s := by
  simp [setShiftTotal, setShiftTotalB, models_iff, Matrix.vecForall_iff, setShift.defined.iff]

theorem pa_proves_setShiftTotal : 𝗣𝗔 ⊢ setShiftTotal :=
  Lib.pa_proves_of_models fun _ _ _ ↦ models_setShiftTotal.mpr fun _ ↦ ⟨_, rfl⟩

theorem lib_setShiftTotal : Lib setShiftTotal := Lib.of_pa pa_proves_setShiftTotal

end ArithS
