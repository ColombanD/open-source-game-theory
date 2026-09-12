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

/-- `x ∈ insert x s`. -/
noncomputable def memInsertSelfB : ArithmeticSemisentence 3 := “t s x. !insertDef t x s → x ∈ t”
noncomputable def memInsertSelf : ArithmeticSentence := ∀¹* memInsertSelfB

lemma models_memInsertSelf :
    V↓[ℒₒᵣ] ⊧ memInsertSelf ↔ ∀ t s x : V, t = insert x s → x ∈ t := by
  simp [memInsertSelf, memInsertSelfB, models_iff, Matrix.vecForall_iff]

theorem pa_proves_memInsertSelf : 𝗣𝗔 ⊢ memInsertSelf :=
  Lib.pa_proves_of_models fun _ _ _ ↦ models_memInsertSelf.mpr fun _ _ _ h ↦ by subst h; simp

theorem lib_memInsertSelf : Lib memInsertSelf := Lib.of_pa pa_proves_memInsertSelf

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

/-- `s ⊆ insert x s`. -/
noncomputable def subsetInsertB : ArithmeticSemisentence 3 :=
  “t s x. !insertDef t x s → !bitSubsetDef s t”
noncomputable def subsetInsert : ArithmeticSentence := ∀¹* subsetInsertB

lemma models_subsetInsert :
    V↓[ℒₒᵣ] ⊧ subsetInsert ↔ ∀ t s x : V, t = insert x s → s ⊆ t := by
  simp [subsetInsert, subsetInsertB, models_iff, Matrix.vecForall_iff]

theorem pa_proves_subsetInsert : 𝗣𝗔 ⊢ subsetInsert :=
  Lib.pa_proves_of_models fun _ _ _ ↦ models_subsetInsert.mpr fun _ _ _ h ↦ by
    subst h; exact susbset_insert _ _

theorem lib_subsetInsert : Lib subsetInsert := Lib.of_pa pa_proves_subsetInsert

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

/-- `∅ ⊆ s` (`∅ = 0`). -/
noncomputable def emptySubsetB : ArithmeticSemisentence 1 := “s. !bitSubsetDef 0 s”
noncomputable def emptySubset : ArithmeticSentence := ∀¹* emptySubsetB

lemma models_emptySubset : V↓[ℒₒᵣ] ⊧ emptySubset ↔ ∀ s : V, (0 : V) ⊆ s := by
  simp [emptySubset, emptySubsetB, models_iff, Matrix.vecForall_iff]

theorem pa_proves_emptySubset : 𝗣𝗔 ⊢ emptySubset :=
  Lib.pa_proves_of_models fun _ _ _ ↦ models_emptySubset.mpr fun s ↦ empty_subset s

theorem lib_emptySubset : Lib emptySubset := Lib.of_pa pa_proves_emptySubset

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

/-- `s ⊆ t → x ∈ s → x ∈ t`. -/
noncomputable def subsetMemB : ArithmeticSemisentence 3 :=
  “x t s. !bitSubsetDef s t → x ∈ s → x ∈ t”
noncomputable def subsetMem : ArithmeticSentence := ∀¹* subsetMemB

lemma models_subsetMem :
    V↓[ℒₒᵣ] ⊧ subsetMem ↔ ∀ x t s : V, s ⊆ t → x ∈ s → x ∈ t := by
  simp [subsetMem, subsetMemB, models_iff, Matrix.vecForall_iff]

theorem pa_proves_subsetMem : 𝗣𝗔 ⊢ subsetMem :=
  Lib.pa_proves_of_models fun _ _ _ ↦ models_subsetMem.mpr fun _ _ _ hst hx ↦ hst hx

theorem lib_subsetMem : Lib subsetMem := Lib.of_pa pa_proves_subsetMem

/-- `s ⊆ s`. -/
noncomputable def subsetReflB : ArithmeticSemisentence 1 := “s. !bitSubsetDef s s”
noncomputable def subsetRefl : ArithmeticSentence := ∀¹* subsetReflB

lemma models_subsetRefl : V↓[ℒₒᵣ] ⊧ subsetRefl ↔ ∀ s : V, s ⊆ s := by
  simp [subsetRefl, subsetReflB, models_iff, Matrix.vecForall_iff]

theorem pa_proves_subsetRefl : 𝗣𝗔 ⊢ subsetRefl :=
  Lib.pa_proves_of_models fun _ _ _ ↦ models_subsetRefl.mpr fun s ↦ subset_refl s

theorem lib_subsetRefl : Lib subsetRefl := Lib.of_pa pa_proves_subsetRefl

/-- `s ⊆ t → t ⊆ u → s ⊆ u`. -/
noncomputable def subsetTransB : ArithmeticSemisentence 3 :=
  “u t s. !bitSubsetDef s t → !bitSubsetDef t u → !bitSubsetDef s u”
noncomputable def subsetTrans : ArithmeticSentence := ∀¹* subsetTransB

lemma models_subsetTrans :
    V↓[ℒₒᵣ] ⊧ subsetTrans ↔ ∀ u t s : V, s ⊆ t → t ⊆ u → s ⊆ u := by
  simp [subsetTrans, subsetTransB, models_iff, Matrix.vecForall_iff]

theorem pa_proves_subsetTrans : 𝗣𝗔 ⊢ subsetTrans :=
  Lib.pa_proves_of_models fun _ _ _ ↦ models_subsetTrans.mpr fun _ _ _ h₁ h₂ ↦ subset_trans h₁ h₂

theorem lib_subsetTrans : Lib subsetTrans := Lib.of_pa pa_proves_subsetTrans

/-! ### `IsFormulaSet` -/

/-- `(∀ x, x ∉ s) → IsFormulaSet s` — emptiness EXTENSIONALLY: a closed numeral `0` inside the
Δ₁ object `isFormulaSet` makes elaboration blow up (the numeral-in-blueprint trap), so the
fragment instantiates this row at `0` and discharges the premise by `notMemEmpty`. -/
noncomputable def isFormulaSetOfNoMemB : ArithmeticSemisentence 1 :=
  “s. (∀ x, x ∉ s) → !(isFormulaSet LAct).sigma s”
noncomputable def isFormulaSetOfNoMem : ArithmeticSentence := ∀¹* isFormulaSetOfNoMemB

lemma models_isFormulaSetOfNoMem :
    V↓[ℒₒᵣ] ⊧ isFormulaSetOfNoMem ↔ ∀ s : V, (∀ x, x ∉ s) → IsFormulaSet LAct s := by
  simp [isFormulaSetOfNoMem, isFormulaSetOfNoMemB, models_iff, Matrix.vecForall_iff]

theorem pa_proves_isFormulaSetOfNoMem : 𝗣𝗔 ⊢ isFormulaSetOfNoMem :=
  Lib.pa_proves_of_models fun _ _ _ ↦ models_isFormulaSetOfNoMem.mpr fun _ h p hp ↦ absurd hp (h p)

theorem lib_isFormulaSetOfNoMem : Lib isFormulaSetOfNoMem := Lib.of_pa pa_proves_isFormulaSetOfNoMem

/-- `x ∉ ∅` (`∅ = 0`). -/
noncomputable def notMemEmptyB : ArithmeticSemisentence 1 := “x. x ∉ 0”
noncomputable def notMemEmpty : ArithmeticSentence := ∀¹* notMemEmptyB

lemma models_notMemEmpty : V↓[ℒₒᵣ] ⊧ notMemEmpty ↔ ∀ x : V, x ∉ (0 : V) := by
  simp [notMemEmpty, notMemEmptyB, models_iff, Matrix.vecForall_iff]

theorem pa_proves_notMemEmpty : 𝗣𝗔 ⊢ notMemEmpty :=
  Lib.pa_proves_of_models fun _ _ _ ↦ models_notMemEmpty.mpr fun x ↦ by simp

theorem lib_notMemEmpty : Lib notMemEmpty := Lib.of_pa pa_proves_notMemEmpty

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

/-- `IsFormulaSet (insert p s) → IsFormulaSet s ∧ IsFormula p`. -/
noncomputable def isFormulaSetInsertInvB : ArithmeticSemisentence 3 :=
  “t p s. !insertDef t p s → !(isFormulaSet LAct).pi t →
    !(isFormulaSet LAct).sigma s ∧ !(isSemiformula LAct).sigma 0 p”
noncomputable def isFormulaSetInsertInv : ArithmeticSentence := ∀¹* isFormulaSetInsertInvB

lemma models_isFormulaSetInsertInv :
    V↓[ℒₒᵣ] ⊧ isFormulaSetInsertInv ↔
    ∀ t p s : V, t = insert p s → IsFormulaSet LAct t → IsFormulaSet LAct s ∧ IsFormula LAct p := by
  simp [isFormulaSetInsertInv, isFormulaSetInsertInvB, models_iff, Matrix.vecForall_iff]

theorem pa_proves_isFormulaSetInsertInv : 𝗣𝗔 ⊢ isFormulaSetInsertInv :=
  Lib.pa_proves_of_models fun _ _ _ ↦ models_isFormulaSetInsertInv.mpr fun _ _ _ h ht ↦ by
    subst h; exact ⟨(IsFormulaSet.insert_iff.mp ht).2, (IsFormulaSet.insert_iff.mp ht).1⟩

theorem lib_isFormulaSetInsertInv : Lib isFormulaSetInsertInv :=
  Lib.of_pa pa_proves_isFormulaSetInsertInv

/-- `IsFormulaSet s → p ∈ s → IsFormula p`. -/
noncomputable def isFormulaSetMemB : ArithmeticSemisentence 2 :=
  “p s. !(isFormulaSet LAct).pi s → p ∈ s → !(isSemiformula LAct).sigma 0 p”
noncomputable def isFormulaSetMem : ArithmeticSentence := ∀¹* isFormulaSetMemB

lemma models_isFormulaSetMem :
    V↓[ℒₒᵣ] ⊧ isFormulaSetMem ↔ ∀ p s : V, IsFormulaSet LAct s → p ∈ s → IsFormula LAct p := by
  simp [isFormulaSetMem, isFormulaSetMemB, models_iff, Matrix.vecForall_iff]

theorem pa_proves_isFormulaSetMem : 𝗣𝗔 ⊢ isFormulaSetMem :=
  Lib.pa_proves_of_models fun _ _ _ ↦ models_isFormulaSetMem.mpr fun p _ hs hp ↦ hs p hp

theorem lib_isFormulaSetMem : Lib isFormulaSetMem := Lib.of_pa pa_proves_isFormulaSetMem

/-! ### Properness bridges (`.sigma ↔ .pi`) -/

noncomputable def isFormulaSetSigmaPiB : ArithmeticSemisentence 1 :=
  “s. !(isFormulaSet LAct).sigma s → !(isFormulaSet LAct).pi s”
noncomputable def isFormulaSetSigmaPi : ArithmeticSentence := ∀¹* isFormulaSetSigmaPiB

lemma models_isFormulaSetSigmaPi :
    V↓[ℒₒᵣ] ⊧ isFormulaSetSigmaPi ↔ ∀ s : V, IsFormulaSet LAct s → IsFormulaSet LAct s := by
  simp [isFormulaSetSigmaPi, isFormulaSetSigmaPiB, models_iff, Matrix.vecForall_iff]

theorem pa_proves_isFormulaSetSigmaPi : 𝗣𝗔 ⊢ isFormulaSetSigmaPi :=
  Lib.pa_proves_of_models fun _ _ _ ↦ models_isFormulaSetSigmaPi.mpr fun _ h ↦ h

theorem lib_isFormulaSetSigmaPi : Lib isFormulaSetSigmaPi := Lib.of_pa pa_proves_isFormulaSetSigmaPi

noncomputable def isFormulaSetPiSigmaB : ArithmeticSemisentence 1 :=
  “s. !(isFormulaSet LAct).pi s → !(isFormulaSet LAct).sigma s”
noncomputable def isFormulaSetPiSigma : ArithmeticSentence := ∀¹* isFormulaSetPiSigmaB

lemma models_isFormulaSetPiSigma :
    V↓[ℒₒᵣ] ⊧ isFormulaSetPiSigma ↔ ∀ s : V, IsFormulaSet LAct s → IsFormulaSet LAct s := by
  simp [isFormulaSetPiSigma, isFormulaSetPiSigmaB, models_iff, Matrix.vecForall_iff]

theorem pa_proves_isFormulaSetPiSigma : 𝗣𝗔 ⊢ isFormulaSetPiSigma :=
  Lib.pa_proves_of_models fun _ _ _ ↦ models_isFormulaSetPiSigma.mpr fun _ h ↦ h

theorem lib_isFormulaSetPiSigma : Lib isFormulaSetPiSigma := Lib.of_pa pa_proves_isFormulaSetPiSigma

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

noncomputable def isSemiformulaPiSigmaB : ArithmeticSemisentence 2 :=
  “p n. !(isSemiformula LAct).pi n p → !(isSemiformula LAct).sigma n p”
noncomputable def isSemiformulaPiSigma : ArithmeticSentence := ∀¹* isSemiformulaPiSigmaB

lemma models_isSemiformulaPiSigma :
    V↓[ℒₒᵣ] ⊧ isSemiformulaPiSigma ↔
    ∀ p n : V, IsSemiformula LAct n p → IsSemiformula LAct n p := by
  simp [isSemiformulaPiSigma, isSemiformulaPiSigmaB, models_iff, Matrix.vecForall_iff]

theorem pa_proves_isSemiformulaPiSigma : 𝗣𝗔 ⊢ isSemiformulaPiSigma :=
  Lib.pa_proves_of_models fun _ _ _ ↦ models_isSemiformulaPiSigma.mpr fun _ _ h ↦ h

theorem lib_isSemiformulaPiSigma : Lib isSemiformulaPiSigma :=
  Lib.of_pa pa_proves_isSemiformulaPiSigma

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

/-- `IsFormulaSet s → IsFormulaSet (setShift s)`. -/
noncomputable def isFormulaSetSetShiftB : ArithmeticSemisentence 2 :=
  “t s. !(setShiftGraph LAct) t s → !(isFormulaSet LAct).pi s → !(isFormulaSet LAct).sigma t”
noncomputable def isFormulaSetSetShift : ArithmeticSentence := ∀¹* isFormulaSetSetShiftB

lemma models_isFormulaSetSetShift :
    V↓[ℒₒᵣ] ⊧ isFormulaSetSetShift ↔
    ∀ t s : V, t = setShift LAct s → IsFormulaSet LAct s → IsFormulaSet LAct t := by
  simp [isFormulaSetSetShift, isFormulaSetSetShiftB, models_iff, Matrix.vecForall_iff,
    setShift.defined.iff]

theorem pa_proves_isFormulaSetSetShift : 𝗣𝗔 ⊢ isFormulaSetSetShift :=
  Lib.pa_proves_of_models fun _ _ _ ↦ models_isFormulaSetSetShift.mpr fun _ _ ht hs ↦ by
    subst ht; exact hs.setShift

theorem lib_isFormulaSetSetShift : Lib isFormulaSetSetShift :=
  Lib.of_pa pa_proves_isFormulaSetSetShift

/-- `IsFormulaSet (setShift s) → IsFormulaSet s`. -/
noncomputable def isFormulaSetOfSetShiftB : ArithmeticSemisentence 2 :=
  “t s. !(setShiftGraph LAct) t s → !(isFormulaSet LAct).pi t → !(isFormulaSet LAct).sigma s”
noncomputable def isFormulaSetOfSetShift : ArithmeticSentence := ∀¹* isFormulaSetOfSetShiftB

lemma models_isFormulaSetOfSetShift :
    V↓[ℒₒᵣ] ⊧ isFormulaSetOfSetShift ↔
    ∀ t s : V, t = setShift LAct s → IsFormulaSet LAct t → IsFormulaSet LAct s := by
  simp [isFormulaSetOfSetShift, isFormulaSetOfSetShiftB, models_iff, Matrix.vecForall_iff,
    setShift.defined.iff]

theorem pa_proves_isFormulaSetOfSetShift : 𝗣𝗔 ⊢ isFormulaSetOfSetShift :=
  Lib.pa_proves_of_models fun _ _ _ ↦ models_isFormulaSetOfSetShift.mpr fun _ _ ht hs ↦ by
    subst ht; exact IsFormulaSet.setShift_iff.mp hs

theorem lib_isFormulaSetOfSetShift : Lib isFormulaSetOfSetShift :=
  Lib.of_pa pa_proves_isFormulaSetOfSetShift

/-! ### Totality -/

/-- `∀ x s, ∃ t, t = insert x s`. -/
noncomputable def insertTotalB : ArithmeticSemisentence 2 := “s x. ∃ t, !insertDef t x s”
noncomputable def insertTotal : ArithmeticSentence := ∀¹* insertTotalB

lemma models_insertTotal : V↓[ℒₒᵣ] ⊧ insertTotal ↔ ∀ s x : V, ∃ t, t = insert x s := by
  simp [insertTotal, insertTotalB, models_iff, Matrix.vecForall_iff]

theorem pa_proves_insertTotal : 𝗣𝗔 ⊢ insertTotal :=
  Lib.pa_proves_of_models fun _ _ _ ↦ models_insertTotal.mpr fun _ _ ↦ ⟨_, rfl⟩

theorem lib_insertTotal : Lib insertTotal := Lib.of_pa pa_proves_insertTotal

/-- `∀ s, ∃ t, t = setShift s`. -/
noncomputable def setShiftTotalB : ArithmeticSemisentence 1 := “s. ∃ t, !(setShiftGraph LAct) t s”
noncomputable def setShiftTotal : ArithmeticSentence := ∀¹* setShiftTotalB

lemma models_setShiftTotal : V↓[ℒₒᵣ] ⊧ setShiftTotal ↔ ∀ s : V, ∃ t, t = setShift LAct s := by
  simp [setShiftTotal, setShiftTotalB, models_iff, Matrix.vecForall_iff, setShift.defined.iff]

theorem pa_proves_setShiftTotal : 𝗣𝗔 ⊢ setShiftTotal :=
  Lib.pa_proves_of_models fun _ _ _ ↦ models_setShiftTotal.mpr fun _ ↦ ⟨_, rfl⟩

theorem lib_setShiftTotal : Lib setShiftTotal := Lib.of_pa pa_proves_setShiftTotal

/-- `∀ p, ∃ q, q = shift p`. -/
noncomputable def shiftTotalB : ArithmeticSemisentence 1 := “p. ∃ q, !(shiftGraph LAct) q p”
noncomputable def shiftTotal : ArithmeticSentence := ∀¹* shiftTotalB

lemma models_shiftTotal : V↓[ℒₒᵣ] ⊧ shiftTotal ↔ ∀ p : V, ∃ q, q = shift LAct p := by
  simp [shiftTotal, shiftTotalB, models_iff, Matrix.vecForall_iff, shift.defined.iff]

theorem pa_proves_shiftTotal : 𝗣𝗔 ⊢ shiftTotal :=
  Lib.pa_proves_of_models fun _ _ _ ↦ models_shiftTotal.mpr fun _ ↦ ⟨_, rfl⟩

theorem lib_shiftTotal : Lib shiftTotal := Lib.of_pa pa_proves_shiftTotal

/-- `∀ p, ∃ q, q = free p`. -/
noncomputable def freeTotalB : ArithmeticSemisentence 1 := “p. ∃ q, !(freeGraph LAct) q p”
noncomputable def freeTotal : ArithmeticSentence := ∀¹* freeTotalB

lemma models_freeTotal : V↓[ℒₒᵣ] ⊧ freeTotal ↔ ∀ p : V, ∃ q, q = free LAct p := by
  simp [freeTotal, freeTotalB, models_iff, Matrix.vecForall_iff, free.defined.iff]

theorem pa_proves_freeTotal : 𝗣𝗔 ⊢ freeTotal :=
  Lib.pa_proves_of_models fun _ _ _ ↦ models_freeTotal.mpr fun _ ↦ ⟨_, rfl⟩

theorem lib_freeTotal : Lib freeTotal := Lib.of_pa pa_proves_freeTotal

end ArithS
