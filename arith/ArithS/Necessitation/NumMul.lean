import ArithS.Necessitation.NumSteps
import ArithS.Necessitation.RowInstB

/-!
# ArithS.Necessitation.NumMul — N4: `bnum a · bnum b = bnum (a · b)` as a derivation code

`M4_BOUNDED_HBL/DESIGN_fragments.md` §2.4 (row N4) and §7 step 8 (the cube `bnum ‖k‖ ·
bnum ‖k‖ · bnum ‖k‖` the budget is compared against): the closed fact `mulFact a b :=
eqFact (bnum a ^* bnum b) (bnum (a * b))` as ONE `sLemma` step. The prover `mulEqCode tblM tbl a b`
is `NumSteps.lean`'s `addCode` pattern — a `Fixpoint` on `⟪a, b, d⟫` recursing on the BITS OF `b`
with `a` fixed — over its own five-row table (`MulTableOK`: `zeroMul`, `mulZero`, `mulOne`, and the
two COMBINED bit rows `twoMulMulS : x·y = z → x·(2y) = 2z` and
`twoMulOneMulS : x·y = z → 2z + x = w → x·(2y + 1) = w`) plus the numeral table (`addCode` for the
odd bit's `2(am) + a`). The combined rows fold the congruence into the bit step so that the
conclusion is SYNTACTICALLY `mulFact a (2m)` / `mulFact a (2m + 1)` (`bnum (2·(am)) = 𝟐 ^* bnum (am)`
for `am ≥ 1`); the case `a = 0` (where `bnum (2·0) = 𝟎`) is its own row.

Delivered: `mulEqCode_proof`, `dlen_mulEqCode_le` (`≤ (‖b‖ + 1) · mulNodeCap`, cubic in the bit
length through `addCode`), `lemmaOK_mulEq`, `stepCost_lemma_mulEq`. A leaf file — `NumTableOK` and
every existing row index stay byte-stable.
-/

namespace ArithS

open FFL FFL.FirstOrder Arithmetic Bootstrapping
open PeanoMinus ISigma0 ISigma1
open FFL.FirstOrder.Arithmetic.Bootstrapping.Arithmetic
open LAct

variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

set_option linter.unusedSimpArgs false
set_option linter.unusedSectionVars false

/-! ## 1. The product fact -/

section mulFact

lemma eqFactB_eq_eqFact' (a b : V) : eqFactB a b = eqFact a b := rfl

/-- **N4's fact**: `mulFact a b := bnum a · bnum b = bnum (a · b)`. -/
noncomputable def mulFact (a b : V) : V := eqFact (bnum a ^* bnum b) (bnum (a * b))
noncomputable def mulFactDef : 𝚺₁.Semisentence 3 := .mkSigma
  “y a b. ∃ ta, !bnumGraph ta a ∧ ∃ tb, !bnumGraph tb b ∧ ∃ p, !qqMulGraph p ta tb ∧
    ∃ tab, !bnumGraph tab (a * b) ∧ !eqFactDef y p tab”
instance mulFact_defined : 𝚺₁-Function₂ (mulFact : V → V → V) via mulFactDef := .mk fun v ↦ by
  simp [mulFactDef, bnum.defined.iff, qqMul_defined.iff, eqFact_defined.iff, mulFact]
instance mulFact_definable : 𝚺₁-Function₂ (mulFact : V → V → V) := mulFact_defined.to_definable

lemma isFormula_mulFact (a b : V) : IsFormula LAct (mulFact a b) :=
  isFormula_eqFact (isSemiterm_qqMul_LAct (isSemiterm_bnum_LAct 0 _) (isSemiterm_bnum_LAct 0 _)) (isSemiterm_bnum_LAct 0 _)

/-- The size parameter of the product node: `a·b + a + b` dominates `a`, `b`, `a·b`. -/
lemma le_mulS_left (a b : V) : a ≤ a * b + a + b := le_trans le_add_self le_self_add
lemma le_mulS_right (a b : V) : b ≤ a * b + a + b := le_add_self
lemma mul_le_mulS (a b : V) : a * b ≤ a * b + a + b := le_trans le_self_add le_self_add

/-- `|mulFact a b| ≤ B·E` once `B ≥ |Peq|` and `E ≥ 12‖a·b + a + b‖ + 3`. -/
lemma formulaLen_mulFact_le {B E a b : V} (hPeq : formulaLen LAct (Peq : V) ≤ B) (hE : 12 * ‖a * b + a + b‖ + 3 ≤ E) :
    formulaLen LAct (mulFact a b) ≤ B * E := by
  have hE1 : 1 ≤ E := le_trans one_le_addE hE
  have h1 : termLen LAct (bnum a ^* bnum b) ≤ E := by
    rw [termLen_qqMulL (isSemiterm_bnum_LAct 0 a).isUTerm (isSemiterm_bnum_LAct 0 b).isUTerm]
    have ha := termLen_bnum_le a
    have hb := termLen_bnum_le b
    have hla := length_monotone (le_mulS_left a b)
    have hlb := length_monotone (le_mulS_right a b)
    calc termLen LAct (bnum a) + termLen LAct (bnum b) + 1 ≤ (6 * ‖a‖ + 1) + (6 * ‖b‖ + 1) + 1 :=
          add_le_add (add_le_add ha hb) le_rfl
      _ ≤ (6 * ‖a * b + a + b‖ + 1) + (6 * ‖a * b + a + b‖ + 1) + 1 :=
          add_le_add (add_le_add (add_le_add (mul_le_mul_of_nonneg_left hla zero_le) le_rfl)
            (add_le_add (mul_le_mul_of_nonneg_left hlb zero_le) le_rfl)) le_rfl
      _ = 12 * ‖a * b + a + b‖ + 3 := by ring
      _ ≤ E := hE
  have h2 : termLen LAct (bnum (a * b)) ≤ E := termLen_bnum_le_E' (mul_le_mulS a b) hE
  exact le_trans (formulaLen_eqFact_le hE1 (isSemiterm_qqMul_LAct (isSemiterm_bnum_LAct 0 _) (isSemiterm_bnum_LAct 0 _))
    (isSemiterm_bnum_LAct 0 _) h1 h2) (mul_le_mul_of_nonneg_right hPeq zero_le)

lemma one_le_mul_of_one_le' {a m : V} (ha : 1 ≤ a) (hm : 1 ≤ m) : 1 ≤ a * m :=
  le_trans ha (le_mul_of_one_le_right zero_le hm)

lemma mulFact_zero_right (a : V) : mulFact a 0 = eqFact (bnum a ^* (𝟎 : V)) (𝟎 : V) := by
  unfold mulFact; rw [mul_zero, bnum_zero]
lemma mulFact_one_right (a : V) : mulFact a 1 = eqFact (bnum a ^* (𝟏 : V)) (bnum a) := by
  unfold mulFact; rw [mul_one, bnum_one]
lemma mulFact_zero_left (b : V) : mulFact 0 b = eqFact ((𝟎 : V) ^* bnum b) (𝟎 : V) := by
  unfold mulFact; rw [zero_mul, bnum_zero]
lemma mulFact_two_mul {a m : V} (ha : 1 ≤ a) (hm : 1 ≤ m) :
    mulFact a (2 * m) = eqFact (bnum a ^* (((𝟏 : V) ^+ (𝟏 : V)) ^* bnum m)) (((𝟏 : V) ^+ (𝟏 : V)) ^* bnum (a * m)) := by
  unfold mulFact
  rw [bnum_two_mul hm, mul_left_comm, bnum_two_mul (one_le_mul_of_one_le' ha hm)]; rfl
lemma mulFact_two_mul_add_one {a m : V} (hm : 1 ≤ m) :
    mulFact a (2 * m + 1) = eqFact (bnum a ^* ((((𝟏 : V) ^+ (𝟏 : V)) ^* bnum m) ^+ (𝟏 : V))) (bnum (a * (2 * m + 1))) := by
  unfold mulFact
  rw [bnum_two_mul_add_one hm]; rfl
lemma addFact_two_mul_mul {a m : V} (ha : 1 ≤ a) (hm : 1 ≤ m) :
    addFact (2 * (a * m)) a = eqFact ((((𝟏 : V) ^+ (𝟏 : V)) ^* bnum (a * m)) ^+ bnum a) (bnum (a * (2 * m + 1))) := by
  unfold addFact
  rw [bnum_two_mul (one_le_mul_of_one_le' ha hm), show 2 * (a * m) + a = a * (2 * m + 1) by ring]; rfl

end mulFact

/-! ## 2. The rows -/

section rows

set_option linter.unusedVariables false

/-- `0 · y = 0`. -/
noncomputable def zeroMulB : ArithmeticSemisentence 1 := “y. (0 * y) = 0”
noncomputable def zeroMul : ArithmeticSentence := ∀¹* zeroMulB
lemma models_zeroMul : V↓[ℒₒᵣ] ⊧ zeroMul ↔ ∀ y : V, (0 : V) * y = 0 := by
  simp [zeroMul, zeroMulB, models_iff, Matrix.vecForall_iff]
theorem pa_proves_zeroMul : 𝗣𝗔 ⊢ zeroMul :=
  Lib.pa_proves_of_models fun _ _ _ ↦ models_zeroMul.mpr fun _ ↦ zero_mul _
theorem lib_zeroMul : Lib zeroMul := Lib.of_pa pa_proves_zeroMul
noncomputable def row_zeroMul_as : List V := []
noncomputable def row_zeroMul_c : V := subst LAct (listToVec [(𝟎 : V) ^* bv 0, (𝟎 : V)]) PeqB
theorem quote_row_zeroMul : (⌜Semiformula.lMap emb zeroMulB⌝ : V) = impChain LAct row_zeroMul_as row_zeroMul_c := by
  unfold zeroMulB row_zeroMul_as row_zeroMul_c PeqB
  all_goals row_shapeB
lemma inst_zeroMul {wy : V} (hwy : IsSemiterm LAct 0 wy) :
    row_zeroMul_as.map (instOuter LAct [wy]) = [] ∧
    instOuter LAct [wy] row_zeroMul_c = eqFactB ((𝟎 : V) ^* wy) (𝟎 : V) := by
  have hes : ∀ e ∈ ([wy] : List V), IsSemiterm LAct 0 e := (List.forall_mem_cons.mpr ⟨hwy, List.forall_mem_nil _⟩)
  unfold row_zeroMul_as row_zeroMul_c
  simp only [List.map_cons, List.map_nil]
  rw [instOuter_subst_listToVec _ isSemiformula_PeqB (by rfl) _ hes (by row_entriesB)]
  all_goals try row_entries_simpB
  row_finish

/-- `x · 0 = 0`. -/
noncomputable def mulZeroB : ArithmeticSemisentence 1 := “x. (x * 0) = 0”
noncomputable def mulZero : ArithmeticSentence := ∀¹* mulZeroB
lemma models_mulZero : V↓[ℒₒᵣ] ⊧ mulZero ↔ ∀ x : V, x * (0 : V) = 0 := by
  simp [mulZero, mulZeroB, models_iff, Matrix.vecForall_iff]
theorem pa_proves_mulZero : 𝗣𝗔 ⊢ mulZero :=
  Lib.pa_proves_of_models fun _ _ _ ↦ models_mulZero.mpr fun _ ↦ mul_zero _
theorem lib_mulZero : Lib mulZero := Lib.of_pa pa_proves_mulZero
noncomputable def row_mulZero_as : List V := []
noncomputable def row_mulZero_c : V := subst LAct (listToVec [bv 0 ^* (𝟎 : V), (𝟎 : V)]) PeqB
theorem quote_row_mulZero : (⌜Semiformula.lMap emb mulZeroB⌝ : V) = impChain LAct row_mulZero_as row_mulZero_c := by
  unfold mulZeroB row_mulZero_as row_mulZero_c PeqB
  all_goals row_shapeB
lemma inst_mulZero {wx : V} (hwx : IsSemiterm LAct 0 wx) :
    row_mulZero_as.map (instOuter LAct [wx]) = [] ∧
    instOuter LAct [wx] row_mulZero_c = eqFactB (wx ^* (𝟎 : V)) (𝟎 : V) := by
  have hes : ∀ e ∈ ([wx] : List V), IsSemiterm LAct 0 e := (List.forall_mem_cons.mpr ⟨hwx, List.forall_mem_nil _⟩)
  unfold row_mulZero_as row_mulZero_c
  simp only [List.map_cons, List.map_nil]
  rw [instOuter_subst_listToVec _ isSemiformula_PeqB (by rfl) _ hes (by row_entriesB)]
  all_goals try row_entries_simpB
  row_finish

/-- `x · 1 = x`. -/
noncomputable def mulOneB : ArithmeticSemisentence 1 := “x. (x * 1) = x”
noncomputable def mulOne : ArithmeticSentence := ∀¹* mulOneB
lemma models_mulOne : V↓[ℒₒᵣ] ⊧ mulOne ↔ ∀ x : V, x * (1 : V) = x := by
  simp [mulOne, mulOneB, models_iff, Matrix.vecForall_iff]
theorem pa_proves_mulOne : 𝗣𝗔 ⊢ mulOne :=
  Lib.pa_proves_of_models fun _ _ _ ↦ models_mulOne.mpr fun _ ↦ mul_one _
theorem lib_mulOne : Lib mulOne := Lib.of_pa pa_proves_mulOne
noncomputable def row_mulOne_as : List V := []
noncomputable def row_mulOne_c : V := subst LAct (listToVec [bv 0 ^* (𝟏 : V), bv 0]) PeqB
theorem quote_row_mulOne : (⌜Semiformula.lMap emb mulOneB⌝ : V) = impChain LAct row_mulOne_as row_mulOne_c := by
  unfold mulOneB row_mulOne_as row_mulOne_c PeqB
  all_goals row_shapeB
lemma inst_mulOne {wx : V} (hwx : IsSemiterm LAct 0 wx) :
    row_mulOne_as.map (instOuter LAct [wx]) = [] ∧
    instOuter LAct [wx] row_mulOne_c = eqFactB (wx ^* (𝟏 : V)) wx := by
  have hes : ∀ e ∈ ([wx] : List V), IsSemiterm LAct 0 e := (List.forall_mem_cons.mpr ⟨hwx, List.forall_mem_nil _⟩)
  unfold row_mulOne_as row_mulOne_c
  simp only [List.map_cons, List.map_nil]
  rw [instOuter_subst_listToVec _ isSemiformula_PeqB (by rfl) _ hes (by row_entriesB)]
  all_goals try row_entries_simpB
  row_finish

/-- `x · y = z → x · (2y) = 2z` (N4, the even bit with the congruence folded in). -/
noncomputable def twoMulMulSB : ArithmeticSemisentence 3 := “z y x. (x * y) = z → (x * (2 * y)) = (2 * z)”
noncomputable def twoMulMulS : ArithmeticSentence := ∀¹* twoMulMulSB
lemma models_twoMulMulS : V↓[ℒₒᵣ] ⊧ twoMulMulS ↔ ∀ z y x : V, x * y = z → x * ((2 : V) * y) = (2 : V) * z := by
  simp [twoMulMulS, twoMulMulSB, models_iff, Matrix.vecForall_iff]
theorem pa_proves_twoMulMulS : 𝗣𝗔 ⊢ twoMulMulS :=
  Lib.pa_proves_of_models fun _ _ _ ↦ models_twoMulMulS.mpr fun _ _ _ h ↦ by subst_vars; exact mul_left_comm _ _ _
theorem lib_twoMulMulS : Lib twoMulMulS := Lib.of_pa pa_proves_twoMulMulS
noncomputable def row_twoMulMulS_as : List V := [subst LAct (listToVec [bv 2 ^* bv 1, bv 0]) PeqB]
noncomputable def row_twoMulMulS_c : V :=
  subst LAct (listToVec [bv 2 ^* (((𝟏 : V) ^+ (𝟏 : V)) ^* bv 1), ((𝟏 : V) ^+ (𝟏 : V)) ^* bv 0]) PeqB
theorem quote_row_twoMulMulS : (⌜Semiformula.lMap emb twoMulMulSB⌝ : V) = impChain LAct row_twoMulMulS_as row_twoMulMulS_c := by
  unfold twoMulMulSB row_twoMulMulS_as row_twoMulMulS_c PeqB
  all_goals row_shapeB
/-- `twoMulMulS` at the witnesses `[wx, wy, wz]`. -/
lemma inst_twoMulMulS {wx wy wz : V} (hwx : IsSemiterm LAct 0 wx) (hwy : IsSemiterm LAct 0 wy) (hwz : IsSemiterm LAct 0 wz) :
    row_twoMulMulS_as.map (instOuter LAct [wx, wy, wz]) = [eqFactB (wx ^* wy) wz] ∧
    instOuter LAct [wx, wy, wz] row_twoMulMulS_c = eqFactB (wx ^* (((𝟏 : V) ^+ (𝟏 : V)) ^* wy)) (((𝟏 : V) ^+ (𝟏 : V)) ^* wz) := by
  have hes : ∀ e ∈ ([wx, wy, wz] : List V), IsSemiterm LAct 0 e :=
    (List.forall_mem_cons.mpr ⟨hwx, List.forall_mem_cons.mpr ⟨hwy, List.forall_mem_cons.mpr ⟨hwz, List.forall_mem_nil _⟩⟩⟩)
  unfold row_twoMulMulS_as row_twoMulMulS_c
  simp only [List.map_cons, List.map_nil]
  rw [instOuter_subst_listToVec _ isSemiformula_PeqB (by rfl) _ hes (by row_entriesB),
    instOuter_subst_listToVec _ isSemiformula_PeqB (by rfl) _ hes (by row_entriesB)]
  all_goals try row_entries_simpB
  row_finish

/-- `x · y = z → 2z + x = w → x · (2y + 1) = w` (N4, the odd bit with the congruence folded in). -/
noncomputable def twoMulOneMulSB : ArithmeticSemisentence 4 :=
  “w z y x. (x * y) = z → ((2 * z) + x) = w → (x * ((2 * y) + 1)) = w”
noncomputable def twoMulOneMulS : ArithmeticSentence := ∀¹* twoMulOneMulSB
lemma models_twoMulOneMulS : V↓[ℒₒᵣ] ⊧ twoMulOneMulS ↔
    ∀ w z y x : V, x * y = z → (2 : V) * z + x = w → x * ((2 : V) * y + 1) = w := by
  simp [twoMulOneMulS, twoMulOneMulSB, models_iff, Matrix.vecForall_iff]
theorem pa_proves_twoMulOneMulS : 𝗣𝗔 ⊢ twoMulOneMulS :=
  Lib.pa_proves_of_models fun _ _ _ ↦ models_twoMulOneMulS.mpr fun _ _ _ _ h₁ h₂ ↦ by subst_vars; ring
theorem lib_twoMulOneMulS : Lib twoMulOneMulS := Lib.of_pa pa_proves_twoMulOneMulS
noncomputable def row_twoMulOneMulS_as : List V :=
  [subst LAct (listToVec [bv 3 ^* bv 2, bv 1]) PeqB, subst LAct (listToVec [(((𝟏 : V) ^+ (𝟏 : V)) ^* bv 1) ^+ bv 3, bv 0]) PeqB]
noncomputable def row_twoMulOneMulS_c : V :=
  subst LAct (listToVec [bv 3 ^* ((((𝟏 : V) ^+ (𝟏 : V)) ^* bv 2) ^+ (𝟏 : V)), bv 0]) PeqB
theorem quote_row_twoMulOneMulS : (⌜Semiformula.lMap emb twoMulOneMulSB⌝ : V) = impChain LAct row_twoMulOneMulS_as row_twoMulOneMulS_c := by
  unfold twoMulOneMulSB row_twoMulOneMulS_as row_twoMulOneMulS_c PeqB
  all_goals row_shapeB
/-- `twoMulOneMulS` at the witnesses `[wx, wy, wz, ww]`. -/
lemma inst_twoMulOneMulS {wx wy wz ww : V} (hwx : IsSemiterm LAct 0 wx) (hwy : IsSemiterm LAct 0 wy)
    (hwz : IsSemiterm LAct 0 wz) (hww : IsSemiterm LAct 0 ww) :
    row_twoMulOneMulS_as.map (instOuter LAct [wx, wy, wz, ww]) =
      [eqFactB (wx ^* wy) wz, eqFactB ((((𝟏 : V) ^+ (𝟏 : V)) ^* wz) ^+ wx) ww] ∧
    instOuter LAct [wx, wy, wz, ww] row_twoMulOneMulS_c = eqFactB (wx ^* ((((𝟏 : V) ^+ (𝟏 : V)) ^* wy) ^+ (𝟏 : V))) ww := by
  have hes : ∀ e ∈ ([wx, wy, wz, ww] : List V), IsSemiterm LAct 0 e :=
    (List.forall_mem_cons.mpr ⟨hwx, List.forall_mem_cons.mpr ⟨hwy, List.forall_mem_cons.mpr ⟨hwz,
      List.forall_mem_cons.mpr ⟨hww, List.forall_mem_nil _⟩⟩⟩⟩)
  unfold row_twoMulOneMulS_as row_twoMulOneMulS_c
  simp only [List.map_cons, List.map_nil]
  rw [instOuter_subst_listToVec _ isSemiformula_PeqB (by rfl) _ hes (by row_entriesB),
    instOuter_subst_listToVec _ isSemiformula_PeqB (by rfl) _ hes (by row_entriesB),
    instOuter_subst_listToVec _ isSemiformula_PeqB (by rfl) _ hes (by row_entriesB)]
  all_goals try row_entries_simpB
  row_finish

end rows

/-! ## 3. The product table -/

section table

def rZeroMul : ℕ := 0
def rMulZero : ℕ := 1
def rMulOne : ℕ := 2
def rTwoMulMul : ℕ := 3
def rTwoMulOneMul : ℕ := 4

lemma cast_rZeroMul : ((rZeroMul : ℕ) : V) = 0 := by simp [rZeroMul]
lemma cast_rMulZero : ((rMulZero : ℕ) : V) = 1 := by simp [rMulZero]
lemma cast_rMulOne : ((rMulOne : ℕ) : V) = 2 := by simp [rMulOne]
lemma cast_rTwoMulMul : ((rTwoMulMul : ℕ) : V) = 3 := by simp [rTwoMulMul]
lemma cast_rTwoMulOneMul : ((rTwoMulOneMul : ℕ) : V) = 4 := by simp [rTwoMulOneMul]

/-- **The product table is sound**: the five rows plus the bound on `Peq`. -/
def MulTableOK (tbl N B : V) : Prop :=
  NumRowOK tbl rZeroMul N B 1 row_zeroMul_as row_zeroMul_c ∧
  NumRowOK tbl rMulZero N B 1 row_mulZero_as row_mulZero_c ∧
  NumRowOK tbl rMulOne N B 1 row_mulOne_as row_mulOne_c ∧
  NumRowOK tbl rTwoMulMul N B 3 row_twoMulMulS_as row_twoMulMulS_c ∧
  NumRowOK tbl rTwoMulOneMul N B 4 row_twoMulOneMulS_as row_twoMulOneMulS_c ∧
  formulaLen LAct (Peq : V) ≤ B ∧
  1 ≤ B

/-- **A product table exists in every model**, with ONE standard pair of bounds. -/
theorem exists_mulTable : ∃ N B : ℕ, ∀ (V : Type) [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁],
    ∃ tbl : V, MulTableOK tbl (N : V) (B : V) := by
  obtain ⟨N0, h0⟩ := (lib_zeroMul).univ_code
  obtain ⟨N1, h1⟩ := (lib_mulZero).univ_code
  obtain ⟨N2, h2⟩ := (lib_mulOne).univ_code
  obtain ⟨N3, h3⟩ := (lib_twoMulMulS).univ_code
  obtain ⟨N4, h4⟩ := (lib_twoMulOneMulS).univ_code
  refine ⟨N0 + N1 + N2 + N3 + N4, rowLen zeroMulB + rowLen mulZeroB + rowLen mulOneB + rowLen twoMulMulSB
    + rowLen twoMulOneMulSB + flen (Rewriting.emb eqS : Semiproposition LAct 2) + 1, fun V _ _ ↦ ?_⟩
  obtain ⟨d0, hd0, hl0⟩ := h0 V
  obtain ⟨d1, hd1, hl1⟩ := h1 V
  obtain ⟨d2, hd2, hl2⟩ := h2 V
  obtain ⟨d3, hd3, hl3⟩ := h3 V
  obtain ⟨d4, hd4, hl4⟩ := h4 V
  refine ⟨vecOf [⟪d0, vecOf row_zeroMul_as, row_zeroMul_c⟫, ⟪d1, vecOf row_mulZero_as, row_mulZero_c⟫,
    ⟪d2, vecOf row_mulOne_as, row_mulOne_c⟫, ⟪d3, vecOf row_twoMulMulS_as, row_twoMulMulS_c⟫,
    ⟪d4, vecOf row_twoMulOneMulS_as, row_twoMulOneMulS_c⟫], ?_⟩
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact numRowOK_of zeroMulB (by unfold rZeroMul; rw [nth_vecOf _ 0 (by simp)]; rfl) quote_row_zeroMul hd0
      (le_trans hl0 (by exact_mod_cast (by omega : N0 ≤ N0 + N1 + N2 + N3 + N4)))
      (by exact_mod_cast (by omega : rowLen zeroMulB ≤ rowLen zeroMulB + rowLen mulZeroB + rowLen mulOneB + rowLen twoMulMulSB + rowLen twoMulOneMulSB + flen (Rewriting.emb eqS : Semiproposition LAct 2) + 1))
  · exact numRowOK_of mulZeroB (by unfold rMulZero; rw [nth_vecOf _ 1 (by simp)]; rfl) quote_row_mulZero hd1
      (le_trans hl1 (by exact_mod_cast (by omega : N1 ≤ N0 + N1 + N2 + N3 + N4)))
      (by exact_mod_cast (by omega : rowLen mulZeroB ≤ rowLen zeroMulB + rowLen mulZeroB + rowLen mulOneB + rowLen twoMulMulSB + rowLen twoMulOneMulSB + flen (Rewriting.emb eqS : Semiproposition LAct 2) + 1))
  · exact numRowOK_of mulOneB (by unfold rMulOne; rw [nth_vecOf _ 2 (by simp)]; rfl) quote_row_mulOne hd2
      (le_trans hl2 (by exact_mod_cast (by omega : N2 ≤ N0 + N1 + N2 + N3 + N4)))
      (by exact_mod_cast (by omega : rowLen mulOneB ≤ rowLen zeroMulB + rowLen mulZeroB + rowLen mulOneB + rowLen twoMulMulSB + rowLen twoMulOneMulSB + flen (Rewriting.emb eqS : Semiproposition LAct 2) + 1))
  · exact numRowOK_of twoMulMulSB (by unfold rTwoMulMul; rw [nth_vecOf _ 3 (by simp)]; rfl) quote_row_twoMulMulS hd3
      (le_trans hl3 (by exact_mod_cast (by omega : N3 ≤ N0 + N1 + N2 + N3 + N4)))
      (by exact_mod_cast (by omega : rowLen twoMulMulSB ≤ rowLen zeroMulB + rowLen mulZeroB + rowLen mulOneB + rowLen twoMulMulSB + rowLen twoMulOneMulSB + flen (Rewriting.emb eqS : Semiproposition LAct 2) + 1))
  · exact numRowOK_of twoMulOneMulSB (by unfold rTwoMulOneMul; rw [nth_vecOf _ 4 (by simp)]; rfl) quote_row_twoMulOneMulS hd4
      (le_trans hl4 (by exact_mod_cast (by omega : N4 ≤ N0 + N1 + N2 + N3 + N4)))
      (by exact_mod_cast (by omega : rowLen twoMulOneMulSB ≤ rowLen zeroMulB + rowLen mulZeroB + rowLen mulOneB + rowLen twoMulMulSB + rowLen twoMulOneMulSB + flen (Rewriting.emb eqS : Semiproposition LAct 2) + 1))
  · rw [Peq, formulaLen_quote_semisentence_V']
    exact_mod_cast (by omega : flen (Rewriting.emb eqS : Semiproposition LAct 2) ≤ rowLen zeroMulB + rowLen mulZeroB + rowLen mulOneB + rowLen twoMulMulSB + rowLen twoMulOneMulSB + flen (Rewriting.emb eqS : Semiproposition LAct 2) + 1)
  · exact_mod_cast (by omega : 1 ≤ rowLen zeroMulB + rowLen mulZeroB + rowLen mulOneB + rowLen twoMulMulSB + rowLen twoMulOneMulSB + flen (Rewriting.emb eqS : Semiproposition LAct 2) + 1)

end table

/-! ## 4. The bit recursion on `b`: `MulGraph tblM tbl a b d` (a `Fixpoint` on `⟪a, b, d⟫`) -/

section mulGraph

namespace MulG

/-- The graph: `⟪a, b, d⟫` where `d` is the product-fact derivation of `(a, b)`. -/
def Phi (tblM tbl : V) (C : Set V) (pr : V) : Prop :=
  ∃ a b d, pr = ⟪a, b, d⟫ ∧
  ( (b = 0 ∧ d = step0 tblM 1 (vecOf [bnum a]) (mulFact a 0)) ∨
    (b = 1 ∧ d = step0 tblM 2 (vecOf [bnum a]) (mulFact a 1)) ∨
    (a = 0 ∧ 2 ≤ b ∧ d = step0 tblM 0 (vecOf [bnum b]) (mulFact 0 b)) ∨
    (∃ m d', 1 ≤ a ∧ 1 ≤ m ∧ b = 2 * m ∧ ⟪a, m, d'⟫ ∈ C ∧
      d = step1 tblM 3 (mulFact a m) d' (vecOf [bnum a, bnum m, bnum (a * m)]) (mulFact a b)) ∨
    (∃ m d', 1 ≤ a ∧ 1 ≤ m ∧ b = 2 * m + 1 ∧ ⟪a, m, d'⟫ ∈ C ∧
      d = step2 tblM 4 (mulFact a m) d' (addFact (2 * (a * m)) a) (addCode tbl (2 * (a * m)) a)
            (vecOf [bnum a, bnum m, bnum (a * m), bnum (a * b)]) (mulFact a b)) )

noncomputable def blueprint : Fixpoint.Blueprint 2 := ⟨.mkDelta
  (.mkSigma “pr C tblM tbl.
    ∃ a <⁺ pr, ∃ q <⁺ pr, !pairDef pr a q ∧ ∃ b <⁺ q, ∃ d <⁺ q, !pairDef q b d ∧
    ( (b = 0 ∧ ∃ ta, !bnumGraph ta a ∧ ∃ ev, !adjoinDef ev ta 0 ∧ ∃ A, !mulFactDef A a 0 ∧
        ∃ x, !step0Def x tblM 1 ev A ∧ d = x) ∨
      (b = 1 ∧ ∃ ta, !bnumGraph ta a ∧ ∃ ev, !adjoinDef ev ta 0 ∧ ∃ A, !mulFactDef A a 1 ∧
        ∃ x, !step0Def x tblM 2 ev A ∧ d = x) ∨
      (a = 0 ∧ 2 ≤ b ∧ ∃ tb, !bnumGraph tb b ∧ ∃ ev, !adjoinDef ev tb 0 ∧ ∃ A, !mulFactDef A 0 b ∧
        ∃ x, !step0Def x tblM 0 ev A ∧ d = x) ∨
      (∃ m < b, ∃ d' < d, 1 ≤ a ∧ 1 ≤ m ∧ b = 2 * m ∧ (∃ q', !pairDef q' m d' ∧ :⟪a, q'⟫:∈ C) ∧
        ∃ F, !mulFactDef F a m ∧ ∃ ta, !bnumGraph ta a ∧ ∃ tm, !bnumGraph tm m ∧ ∃ tam, !bnumGraph tam (a * m) ∧
        ∃ v0, !adjoinDef v0 tam 0 ∧ ∃ v1, !adjoinDef v1 tm v0 ∧ ∃ ev, !adjoinDef ev ta v1 ∧
        ∃ A, !mulFactDef A a b ∧ ∃ x, !step1Def x tblM 3 F d' ev A ∧ d = x) ∨
      (∃ m < b, ∃ d' < d, 1 ≤ a ∧ 1 ≤ m ∧ b = 2 * m + 1 ∧ (∃ q', !pairDef q' m d' ∧ :⟪a, q'⟫:∈ C) ∧
        ∃ F, !mulFactDef F a m ∧ ∃ G, !addFactDef G (2 * (a * m)) a ∧ ∃ dG, !addCodeDef dG tbl (2 * (a * m)) a ∧
        ∃ ta, !bnumGraph ta a ∧ ∃ tm, !bnumGraph tm m ∧ ∃ tam, !bnumGraph tam (a * m) ∧ ∃ tab, !bnumGraph tab (a * b) ∧
        ∃ v0, !adjoinDef v0 tab 0 ∧ ∃ v1, !adjoinDef v1 tam v0 ∧ ∃ v2, !adjoinDef v2 tm v1 ∧ ∃ ev, !adjoinDef ev ta v2 ∧
        ∃ A, !mulFactDef A a b ∧ ∃ x, !step2Def x tblM 4 F d' G dG ev A ∧ d = x) )”)
  (.mkPi “pr C tblM tbl.
    ∃ a <⁺ pr, ∃ q <⁺ pr, !pairDef pr a q ∧ ∃ b <⁺ q, ∃ d <⁺ q, !pairDef q b d ∧
    ( (b = 0 ∧ ∀ ta, !bnumGraph ta a → ∀ ev, !adjoinDef ev ta 0 → ∀ A, !mulFactDef A a 0 →
        ∀ x, !step0Def x tblM 1 ev A → d = x) ∨
      (b = 1 ∧ ∀ ta, !bnumGraph ta a → ∀ ev, !adjoinDef ev ta 0 → ∀ A, !mulFactDef A a 1 →
        ∀ x, !step0Def x tblM 2 ev A → d = x) ∨
      (a = 0 ∧ 2 ≤ b ∧ ∀ tb, !bnumGraph tb b → ∀ ev, !adjoinDef ev tb 0 → ∀ A, !mulFactDef A 0 b →
        ∀ x, !step0Def x tblM 0 ev A → d = x) ∨
      (∃ m < b, ∃ d' < d, 1 ≤ a ∧ 1 ≤ m ∧ b = 2 * m ∧ (∀ q', !pairDef q' m d' → :⟪a, q'⟫:∈ C) ∧
        ∀ F, !mulFactDef F a m → ∀ ta, !bnumGraph ta a → ∀ tm, !bnumGraph tm m → ∀ tam, !bnumGraph tam (a * m) →
        ∀ v0, !adjoinDef v0 tam 0 → ∀ v1, !adjoinDef v1 tm v0 → ∀ ev, !adjoinDef ev ta v1 →
        ∀ A, !mulFactDef A a b → ∀ x, !step1Def x tblM 3 F d' ev A → d = x) ∨
      (∃ m < b, ∃ d' < d, 1 ≤ a ∧ 1 ≤ m ∧ b = 2 * m + 1 ∧ (∀ q', !pairDef q' m d' → :⟪a, q'⟫:∈ C) ∧
        ∀ F, !mulFactDef F a m → ∀ G, !addFactDef G (2 * (a * m)) a → ∀ dG, !addCodeDef dG tbl (2 * (a * m)) a →
        ∀ ta, !bnumGraph ta a → ∀ tm, !bnumGraph tm m → ∀ tam, !bnumGraph tam (a * m) → ∀ tab, !bnumGraph tab (a * b) →
        ∀ v0, !adjoinDef v0 tab 0 → ∀ v1, !adjoinDef v1 tam v0 → ∀ v2, !adjoinDef v2 tm v1 → ∀ ev, !adjoinDef ev ta v2 →
        ∀ A, !mulFactDef A a b → ∀ x, !step2Def x tblM 4 F d' G dG ev A → d = x) )”)⟩

/-- `Phi` with the bounds the blueprint carries. -/
private lemma phi_iff (tblM tbl C pr : V) :
    Phi tblM tbl {x | x ∈ C} pr ↔
    ∃ a ≤ pr, ∃ q ≤ pr, pr = ⟪a, q⟫ ∧ ∃ b ≤ q, ∃ d ≤ q, q = ⟪b, d⟫ ∧
    ( (b = 0 ∧ d = step0 tblM 1 (vecOf [bnum a]) (mulFact a 0)) ∨
      (b = 1 ∧ d = step0 tblM 2 (vecOf [bnum a]) (mulFact a 1)) ∨
      (a = 0 ∧ 2 ≤ b ∧ d = step0 tblM 0 (vecOf [bnum b]) (mulFact 0 b)) ∨
      (∃ m < b, ∃ d' < d, 1 ≤ a ∧ 1 ≤ m ∧ b = 2 * m ∧ ⟪a, m, d'⟫ ∈ C ∧
        d = step1 tblM 3 (mulFact a m) d' (vecOf [bnum a, bnum m, bnum (a * m)]) (mulFact a b)) ∨
      (∃ m < b, ∃ d' < d, 1 ≤ a ∧ 1 ≤ m ∧ b = 2 * m + 1 ∧ ⟪a, m, d'⟫ ∈ C ∧
        d = step2 tblM 4 (mulFact a m) d' (addFact (2 * (a * m)) a) (addCode tbl (2 * (a * m)) a)
              (vecOf [bnum a, bnum m, bnum (a * m), bnum (a * b)]) (mulFact a b)) ) := by
  constructor
  · rintro ⟨a, b, d, rfl, h⟩
    refine ⟨a, le_pair_left _ _, ⟪b, d⟫, le_pair_right _ _, rfl, b, le_pair_left _ _, d, le_pair_right _ _, rfl, ?_⟩
    rcases h with h | h | h | ⟨m, d', ha, hm, rfl, hC, rfl⟩ | ⟨m, d', ha, hm, rfl, hC, rfl⟩
    · exact Or.inl h
    · exact Or.inr (Or.inl h)
    · exact Or.inr (Or.inr (Or.inl h))
    · exact Or.inr (Or.inr (Or.inr (Or.inl
        ⟨m, Bnum.lt_two_mul hm, d', SuccG.d_lt_step1 _ _ _ _ _ _, ha, hm, rfl, hC, rfl⟩)))
    · exact Or.inr (Or.inr (Or.inr (Or.inr
        ⟨m, Bnum.lt_two_mul_add_one hm, d', d_lt_step2 _ _ _ _ _ _ _ _, ha, hm, rfl, hC, rfl⟩)))
  · rintro ⟨a, _, q, _, rfl, b, _, d, _, rfl, h⟩
    refine ⟨a, b, d, rfl, ?_⟩
    rcases h with h | h | h | ⟨m, _, d', _, ha, hm, rfl, hC, rfl⟩ | ⟨m, _, d', _, ha, hm, rfl, hC, rfl⟩
    · exact Or.inl h
    · exact Or.inr (Or.inl h)
    · exact Or.inr (Or.inr (Or.inl h))
    · exact Or.inr (Or.inr (Or.inr (Or.inl ⟨m, d', ha, hm, rfl, hC, rfl⟩)))
    · exact Or.inr (Or.inr (Or.inr (Or.inr ⟨m, d', ha, hm, rfl, hC, rfl⟩)))

set_option maxHeartbeats 3000000 in
noncomputable def construction : Fixpoint.Construction V blueprint where
  Φ := fun v ↦ Phi (v 0) (v 1)
  defined := .mk <| by
    constructor
    · intro v
      simp [blueprint, mulFact_defined.iff, addFact_defined.iff, addCode_defined.iff, bnum.defined.iff,
        step0_defined.iff, step1_defined.iff, step2_defined.iff, numeral_eq_natCast]
    · intro v
      symm
      simpa [blueprint, mulFact_defined.iff, addFact_defined.iff, addCode_defined.iff, bnum.defined.iff,
        step0_defined.iff, step1_defined.iff, step2_defined.iff, numeral_eq_natCast] using phi_iff (v 2) (v 3) (v 1) (v 0)
  monotone := by
    rintro C C' hC _ pr ⟨a, b, d, rfl, h⟩
    refine ⟨a, b, d, rfl, ?_⟩
    rcases h with h | h | h | ⟨m, d', ha, hm, rfl, hC', rfl⟩ | ⟨m, d', ha, hm, rfl, hC', rfl⟩
    · exact Or.inl h
    · exact Or.inr (Or.inl h)
    · exact Or.inr (Or.inr (Or.inl h))
    · exact Or.inr (Or.inr (Or.inr (Or.inl ⟨m, d', ha, hm, rfl, hC hC', rfl⟩)))
    · exact Or.inr (Or.inr (Or.inr (Or.inr ⟨m, d', ha, hm, rfl, hC hC', rfl⟩)))

instance : construction.Finite V where
  finite := by
    rintro C _ pr ⟨a, b, d, rfl, h⟩
    rcases h with h | h | h | ⟨m, d', ha, hm, rfl, hC', rfl⟩ | ⟨m, d', ha, hm, rfl, hC', rfl⟩
    · exact ⟨0, a, b, d, rfl, Or.inl h⟩
    · exact ⟨0, a, b, d, rfl, Or.inr (Or.inl h)⟩
    · exact ⟨0, a, b, d, rfl, Or.inr (Or.inr (Or.inl h))⟩
    · exact ⟨⟪a, m, d'⟫ + 1, _, _, _, rfl, Or.inr (Or.inr (Or.inr (Or.inl
        ⟨m, d', ha, hm, rfl, ⟨hC', lt_add_one _⟩, rfl⟩)))⟩
    · exact ⟨⟪a, m, d'⟫ + 1, _, _, _, rfl, Or.inr (Or.inr (Or.inr (Or.inr
        ⟨m, d', ha, hm, rfl, ⟨hC', lt_add_one _⟩, rfl⟩)))⟩

end MulG

/-- `MulGraph tblM tbl a b d`: `d` is the product-fact derivation of `(a, b)` over the tables. -/
def MulGraph (tblM tbl a b d : V) : Prop := MulG.construction.Fixpoint ![tblM, tbl] ⟪a, b, d⟫

noncomputable def mulGraphDef : 𝚺₁.Semisentence 5 := .mkSigma
  “tblM tbl a b d. ∃ q, !pairDef q b d ∧ ∃ p, !pairDef p a q ∧ !MulG.blueprint.fixpointDef p tblM tbl”

instance mulGraph_defined :
    𝚺₁.Defined (fun v : Fin 5 → V ↦ MulGraph (v 0) (v 1) (v 2) (v 3) (v 4)) mulGraphDef := .mk fun v ↦ by
  simp [mulGraphDef, MulG.construction.eval_fixpointDef, MulGraph]
instance mulGraph_definable : 𝚺₁.Definable (fun v : Fin 5 → V ↦ MulGraph (v 0) (v 1) (v 2) (v 3) (v 4)) :=
  mulGraph_defined.to_definable

lemma MulGraph.case_iff {tblM tbl a b d : V} :
    MulGraph tblM tbl a b d ↔
    (b = 0 ∧ d = step0 tblM 1 (vecOf [bnum a]) (mulFact a 0)) ∨
    (b = 1 ∧ d = step0 tblM 2 (vecOf [bnum a]) (mulFact a 1)) ∨
    (a = 0 ∧ 2 ≤ b ∧ d = step0 tblM 0 (vecOf [bnum b]) (mulFact 0 b)) ∨
    (∃ m d', 1 ≤ a ∧ 1 ≤ m ∧ b = 2 * m ∧ MulGraph tblM tbl a m d' ∧
      d = step1 tblM 3 (mulFact a m) d' (vecOf [bnum a, bnum m, bnum (a * m)]) (mulFact a b)) ∨
    (∃ m d', 1 ≤ a ∧ 1 ≤ m ∧ b = 2 * m + 1 ∧ MulGraph tblM tbl a m d' ∧
      d = step2 tblM 4 (mulFact a m) d' (addFact (2 * (a * m)) a) (addCode tbl (2 * (a * m)) a)
            (vecOf [bnum a, bnum m, bnum (a * m), bnum (a * b)]) (mulFact a b)) :=
  Iff.trans MulG.construction.case (by simp [MulG.construction, MulG.Phi, MulGraph])

lemma MulGraph.zero_iff {tblM tbl a d : V} : MulGraph tblM tbl a 0 d ↔ d = step0 tblM 1 (vecOf [bnum a]) (mulFact a 0) := by
  rw [MulGraph.case_iff]
  constructor
  · rintro (⟨_, rfl⟩ | ⟨h, _⟩ | ⟨_, h, _⟩ | ⟨m, _, _, hm, h, _⟩ | ⟨m, _, _, hm, h, _⟩)
    · rfl
    · exact absurd h.symm Arithmetic.one_ne_zero
    · exact absurd h not_two_le_zero
    · exact absurd h (zero_ne_two_mul hm)
    · exact absurd h (zero_ne_two_mul_add_one m)
  · rintro rfl; exact Or.inl ⟨rfl, rfl⟩

lemma MulGraph.one_iff {tblM tbl a d : V} : MulGraph tblM tbl a 1 d ↔ d = step0 tblM 2 (vecOf [bnum a]) (mulFact a 1) := by
  rw [MulGraph.case_iff]
  constructor
  · rintro (⟨h, _⟩ | ⟨_, rfl⟩ | ⟨_, h, _⟩ | ⟨m, _, _, hm, h, _⟩ | ⟨m, _, _, hm, h, _⟩)
    · exact absurd h Arithmetic.one_ne_zero
    · rfl
    · exact absurd h not_two_le_one
    · exact absurd h (one_ne_two_mul hm)
    · exact absurd h (one_ne_two_mul_add_one hm)
  · rintro rfl; exact Or.inr (Or.inl ⟨rfl, rfl⟩)

lemma MulGraph.zero_left_iff {tblM tbl b d : V} (hb : 2 ≤ b) :
    MulGraph tblM tbl 0 b d ↔ d = step0 tblM 0 (vecOf [bnum b]) (mulFact 0 b) := by
  rw [MulGraph.case_iff]
  constructor
  · rintro (⟨h, _⟩ | ⟨h, _⟩ | ⟨_, _, rfl⟩ | ⟨m, _, ha, _, _, _⟩ | ⟨m, _, ha, _, _, _⟩)
    · exact absurd (h ▸ hb) not_two_le_zero
    · exact absurd (h ▸ hb) not_two_le_one
    · rfl
    · exact absurd ha not_one_le_zero
    · exact absurd ha not_one_le_zero
  · rintro rfl; exact Or.inr (Or.inr (Or.inl ⟨rfl, hb, rfl⟩))

lemma MulGraph.two_mul_iff {tblM tbl a m d : V} (ha : 1 ≤ a) (hm : 1 ≤ m) :
    MulGraph tblM tbl a (2 * m) d ↔ ∃ d', MulGraph tblM tbl a m d' ∧
      d = step1 tblM 3 (mulFact a m) d' (vecOf [bnum a, bnum m, bnum (a * m)]) (mulFact a (2 * m)) := by
  rw [MulGraph.case_iff]
  constructor
  · rintro (⟨h, _⟩ | ⟨h, _⟩ | ⟨h, _, _⟩ | ⟨m', d', _, _, h, hd', rfl⟩ | ⟨m', _, _, _, h, _⟩)
    · exact absurd h (two_mul_ne_zero hm)
    · exact absurd h (two_mul_ne_one m)
    · exact absurd (h ▸ ha) not_one_le_zero
    · obtain rfl := two_mul_inj h; exact ⟨d', hd', rfl⟩
    · exact absurd h (two_mul_ne_two_mul_add_one m m')
  · rintro ⟨d', hd', rfl⟩; exact Or.inr (Or.inr (Or.inr (Or.inl ⟨m, d', ha, hm, rfl, hd', rfl⟩)))

lemma MulGraph.two_mul_add_one_iff {tblM tbl a m d : V} (ha : 1 ≤ a) (hm : 1 ≤ m) :
    MulGraph tblM tbl a (2 * m + 1) d ↔ ∃ d', MulGraph tblM tbl a m d' ∧
      d = step2 tblM 4 (mulFact a m) d' (addFact (2 * (a * m)) a) (addCode tbl (2 * (a * m)) a)
            (vecOf [bnum a, bnum m, bnum (a * m), bnum (a * (2 * m + 1))]) (mulFact a (2 * m + 1)) := by
  rw [MulGraph.case_iff]
  constructor
  · rintro (⟨h, _⟩ | ⟨h, _⟩ | ⟨h, _, _⟩ | ⟨m', _, _, _, h, _⟩ | ⟨m', d', _, _, h, hd', rfl⟩)
    · exact absurd h (two_mul_add_one_ne_zero m)
    · exact absurd h (two_mul_add_one_ne_one hm)
    · exact absurd (h ▸ ha) not_one_le_zero
    · exact absurd h.symm (two_mul_ne_two_mul_add_one m' m)
    · obtain rfl := two_mul_add_one_inj h; exact ⟨d', hd', rfl⟩
  · rintro ⟨d', hd', rfl⟩; exact Or.inr (Or.inr (Or.inr (Or.inr ⟨m, d', ha, hm, rfl, hd', rfl⟩)))

lemma mulGraph_exists (tblM tbl a b : V) : ∃ d, MulGraph tblM tbl a b d := by
  induction b using ISigma1.sigma1_order_induction with
  | hP => definability
  | ind b ih =>
    rcases zero_one_or_two_le b with rfl | rfl | h2
    · exact ⟨_, MulGraph.zero_iff.mpr rfl⟩
    · exact ⟨_, MulGraph.one_iff.mpr rfl⟩
    rcases zero_one_or_two_le a with rfl | rfl | ha2
    · exact ⟨_, (MulGraph.zero_left_iff h2).mpr rfl⟩
    · obtain ⟨hm, hlt, he | ho⟩ := two_le_cases h2
      · obtain ⟨d', hd'⟩ := ih (b / 2) hlt
        rw [he]; exact ⟨_, (MulGraph.two_mul_iff le_rfl hm).mpr ⟨d', hd', rfl⟩⟩
      · obtain ⟨d', hd'⟩ := ih (b / 2) hlt
        rw [ho]; exact ⟨_, (MulGraph.two_mul_add_one_iff le_rfl hm).mpr ⟨d', hd', rfl⟩⟩
    · have ha : 1 ≤ a := le_trans one_le_two ha2
      obtain ⟨hm, hlt, he | ho⟩ := two_le_cases h2
      · obtain ⟨d', hd'⟩ := ih (b / 2) hlt
        rw [he]; exact ⟨_, (MulGraph.two_mul_iff ha hm).mpr ⟨d', hd', rfl⟩⟩
      · obtain ⟨d', hd'⟩ := ih (b / 2) hlt
        rw [ho]; exact ⟨_, (MulGraph.two_mul_add_one_iff ha hm).mpr ⟨d', hd', rfl⟩⟩

lemma mulGraph_unique (tblM tbl a b : V) : ∀ d₁ d₂, MulGraph tblM tbl a b d₁ → MulGraph tblM tbl a b d₂ → d₁ = d₂ := by
  induction b using ISigma1.pi1_order_induction with
  | hP => definability
  | ind b ih =>
    intro d₁ d₂ h₁ h₂
    rcases zero_one_or_two_le b with rfl | rfl | h2
    · rw [MulGraph.zero_iff] at h₁ h₂; rw [h₁, h₂]
    · rw [MulGraph.one_iff] at h₁ h₂; rw [h₁, h₂]
    rcases zero_one_or_two_le a with rfl | rfl | ha2
    · rw [MulGraph.zero_left_iff h2] at h₁ h₂; rw [h₁, h₂]
    · obtain ⟨hm, hlt, he | ho⟩ := two_le_cases h2
      · rw [he] at h₁ h₂
        obtain ⟨e₁, he₁, rfl⟩ := (MulGraph.two_mul_iff le_rfl hm).mp h₁
        obtain ⟨e₂, he₂, rfl⟩ := (MulGraph.two_mul_iff le_rfl hm).mp h₂
        rw [ih (b / 2) hlt e₁ e₂ he₁ he₂]
      · rw [ho] at h₁ h₂
        obtain ⟨e₁, he₁, rfl⟩ := (MulGraph.two_mul_add_one_iff le_rfl hm).mp h₁
        obtain ⟨e₂, he₂, rfl⟩ := (MulGraph.two_mul_add_one_iff le_rfl hm).mp h₂
        rw [ih (b / 2) hlt e₁ e₂ he₁ he₂]
    · have ha : 1 ≤ a := le_trans one_le_two ha2
      obtain ⟨hm, hlt, he | ho⟩ := two_le_cases h2
      · rw [he] at h₁ h₂
        obtain ⟨e₁, he₁, rfl⟩ := (MulGraph.two_mul_iff ha hm).mp h₁
        obtain ⟨e₂, he₂, rfl⟩ := (MulGraph.two_mul_iff ha hm).mp h₂
        rw [ih (b / 2) hlt e₁ e₂ he₁ he₂]
      · rw [ho] at h₁ h₂
        obtain ⟨e₁, he₁, rfl⟩ := (MulGraph.two_mul_add_one_iff ha hm).mp h₁
        obtain ⟨e₂, he₂, rfl⟩ := (MulGraph.two_mul_add_one_iff ha hm).mp h₂
        rw [ih (b / 2) hlt e₁ e₂ he₁ he₂]

lemma mulGraph_existsUnique (tblM tbl a b : V) : ∃! d, MulGraph tblM tbl a b d := by
  obtain ⟨d, hd⟩ := mulGraph_exists tblM tbl a b
  exact ExistsUnique.intro d hd (fun d' h' ↦ mulGraph_unique tblM tbl a b d' d h' hd)

/-- **N4's prover**: the derivation code of `{bnum a · bnum b = bnum (a · b)}`. -/
noncomputable def mulEqCode (tblM tbl a b : V) : V := Classical.choose! (mulGraph_existsUnique tblM tbl a b)

lemma mulEqCode_graph (tblM tbl a b : V) : MulGraph tblM tbl a b (mulEqCode tblM tbl a b) :=
  Classical.choose!_spec (mulGraph_existsUnique tblM tbl a b)

lemma mulEqCode_eq_of_graph {tblM tbl a b d : V} (h : MulGraph tblM tbl a b d) : mulEqCode tblM tbl a b = d :=
  mulGraph_unique tblM tbl a b _ _ (mulEqCode_graph tblM tbl a b) h

noncomputable def mulEqCodeDef : 𝚺₁.Semisentence 5 := .mkSigma “y tblM tbl a b. !mulGraphDef tblM tbl a b y”

/-- The `succCode_defined` pattern: never a blanket `simp` through the fixpoint formula. -/
instance mulEqCode_defined : 𝚺₁-Function₄ (mulEqCode : V → V → V → V → V) via mulEqCodeDef := .mk fun v ↦ by
  simp only [mulEqCodeDef]
  rw [HierarchySymbol.Semiformula.val_mkSigma, Semiformula.eval_substs ![#1, #2, #3, #4, #0] mulGraphDef.val,
    mulGraph_defined.iff]
  simp only [Function.comp_apply, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_two,
    Matrix.tail_cons, Matrix.cons_val_three, Matrix.cons_val_four, Semiterm.val_bvar, Fin.succ_zero_eq_one,
    Fin.succ_one_eq_two]
  constructor
  · intro h; exact (mulEqCode_eq_of_graph h).symm
  · intro h; rw [h]; exact mulEqCode_graph _ _ _ _
instance mulEqCode_definable : 𝚺₁-Function₄ (mulEqCode : V → V → V → V → V) := mulEqCode_defined.to_definable

end mulGraph

/-! ## 5. Soundness and length of `mulEqCode`; its `sLemma` packaging

With `s := a·b + a + b` and `E := 12‖s‖ + 3`: every witness and fact of a node is `≤ B·E`; the odd
bit's `addCode (2(am)) a` is `≤ (‖s‖ + 1)(‖s‖ + 2) · nodeCost N B E`; per node
`mulNodeCap := nodeCost N' B' E + (‖s‖ + 1)(‖s‖ + 2) · nodeCost N B E`, monotone in `s`; `‖b‖ + 1`
nodes: `mulEqBound := (‖b‖ + 1) · mulNodeCap` — cubic in the bit length. -/

section mulSound

noncomputable def mulNodeCap (N B N' B' s : V) : V :=
  nodeCost N' B' (12 * ‖s‖ + 3) + (‖s‖ + 1) * (‖s‖ + 2) * nodeCost N B (12 * ‖s‖ + 3)
noncomputable def mulEqBound (N B N' B' a b : V) : V := (‖b‖ + 1) * mulNodeCap N B N' B' (a * b + a + b)

lemma mulNodeCap_mono {N B N' B' s s' : V} (h : s ≤ s') : mulNodeCap N B N' B' s ≤ mulNodeCap N B N' B' s' := by
  unfold mulNodeCap
  have hl := length_monotone h
  have hE : 12 * ‖s‖ + 3 ≤ 12 * ‖s'‖ + 3 := add_le_add (mul_le_mul_of_nonneg_left hl zero_le) le_rfl
  refine add_le_add (nodeCost_mono hE) ?_
  exact mul_le_mul (mul_le_mul (add_le_add hl le_rfl) (add_le_add hl le_rfl) zero_le zero_le) (nodeCost_mono hE)
    zero_le zero_le

lemma mulS_mono_right {a m b : V} (h : m ≤ b) : a * m + a + m ≤ a * b + a + b :=
  add_le_add (add_le_add (mul_le_mul_of_nonneg_left h zero_le) le_rfl) h

lemma mulE_mono {s s' : V} (h : s ≤ s') : 12 * ‖s‖ + 3 ≤ 12 * ‖s'‖ + 3 :=
  add_le_add (mul_le_mul_of_nonneg_left (length_monotone h) zero_le) le_rfl

/-- The odd bit's addition sub-derivation, capped at the node's size. -/
lemma dlen_addCode_mul_le {tbl N B : V} (htbl : NumTableOK tbl N B) {a m : V} (hm : 1 ≤ m) :
    dlen TAct (addCode tbl (2 * (a * m)) a) ≤
      (‖a * (2 * m + 1) + a + (2 * m + 1)‖ + 1) * (‖a * (2 * m + 1) + a + (2 * m + 1)‖ + 2)
        * nodeCost N B (12 * ‖a * (2 * m + 1) + a + (2 * m + 1)‖ + 3) := by
  refine le_trans (dlen_addCode_le htbl _ _) ?_
  have e : 2 * (a * m) + a = a * (2 * m + 1) := by ring
  rw [e]
  have h1 : a * (2 * m + 1) ≤ a * (2 * m + 1) + a + (2 * m + 1) := mul_le_mulS _ _
  have h2 : 2 * (a * m) ≤ a * (2 * m + 1) + a + (2 * m + 1) := by
    refine le_trans ?_ h1
    rw [show a * (2 * m + 1) = 2 * (a * m) + a by ring]; exact le_self_add
  have l1 := length_monotone h1
  have l2 := length_monotone h2
  exact mul_le_mul (mul_le_mul (add_le_add l2 le_rfl) (add_le_add l1 le_rfl) zero_le zero_le)
    (nodeCost_mono (mulE_mono h1)) zero_le zero_le

/-- **Soundness and length of the product chain**, by Π₁ order induction on `b` (`a` fixed). -/
theorem mulGraph_sound {tbl N B tblM N' B' : V} (htbl : NumTableOK tbl N B) (htblM : MulTableOK tblM N' B') (a b : V) :
    ∀ d, MulGraph tblM tbl a b d →
      DerivationOf TAct d (sing (mulFact a b)) ∧ dlen TAct d ≤ mulEqBound N B N' B' a b := by
  induction b using ISigma1.pi1_order_induction with
  | hP => simp only [mulEqBound, mulNodeCap]; definability
  | ind b ih =>
    intro d hd
    obtain ⟨hr0, hr1, hr2, hr3, hr4, hPeq, hB⟩ := htblM
    have hxa : IsSemiterm LAct 0 (bnum a) := isSemiterm_bnum_LAct 0 _
    rcases zero_one_or_two_le b with rfl | rfl | h2
    · rw [MulGraph.zero_iff] at hd
      subst hd
      have hc : instOuter LAct [bnum a] row_mulZero_c = mulFact a 0 := by
        rw [(inst_mulZero hxa).2, mulFact_zero_right]; rfl
      have hes : ∀ e ∈ [bnum a], IsSemiterm LAct 0 e ∧ termLen LAct e ≤ 12 * ‖a * 0 + a + 0‖ + 3 := by
        simp only [List.mem_singleton, forall_eq]
        exact ⟨hxa, termLen_bnum_le_E' (le_mulS_left a 0) le_rfl⟩
      have hpf := step0_proof hr1 [bnum a] rfl (fun e he ↦ (hes e he).1) (isFormula_mulFact a 0) (inst_mulZero hxa).1 hc
      have hlen := dlen_step0_le hr1 [bnum a] rfl hes one_le_addE hB (isFormula_mulFact a 0) (inst_mulZero hxa).1 hc
        (by norm_num) (by simp [row_mulZero_as]) (formulaLen_mulFact_le hPeq le_rfl)
      rw [cast_rMulZero] at hpf hlen
      refine ⟨hpf, ?_⟩
      unfold mulEqBound mulNodeCap
      exact le_trans hlen (le_trans le_self_add (le_mul_of_one_le_left zero_le le_add_self))
    · rw [MulGraph.one_iff] at hd
      subst hd
      have hc : instOuter LAct [bnum a] row_mulOne_c = mulFact a 1 := by
        rw [(inst_mulOne hxa).2, mulFact_one_right]; rfl
      have hes : ∀ e ∈ [bnum a], IsSemiterm LAct 0 e ∧ termLen LAct e ≤ 12 * ‖a * 1 + a + 1‖ + 3 := by
        simp only [List.mem_singleton, forall_eq]
        exact ⟨hxa, termLen_bnum_le_E' (le_mulS_left a 1) le_rfl⟩
      have hpf := step0_proof hr2 [bnum a] rfl (fun e he ↦ (hes e he).1) (isFormula_mulFact a 1) (inst_mulOne hxa).1 hc
      have hlen := dlen_step0_le hr2 [bnum a] rfl hes one_le_addE hB (isFormula_mulFact a 1) (inst_mulOne hxa).1 hc
        (by norm_num) (by simp [row_mulOne_as]) (formulaLen_mulFact_le hPeq le_rfl)
      rw [cast_rMulOne] at hpf hlen
      refine ⟨hpf, ?_⟩
      unfold mulEqBound mulNodeCap
      exact le_trans hlen (le_trans le_self_add (le_mul_of_one_le_left zero_le le_add_self))
    by_cases ha0 : a = 0
    · subst ha0
      rw [MulGraph.zero_left_iff h2] at hd
      subst hd
      have hxb : IsSemiterm LAct 0 (bnum b) := isSemiterm_bnum_LAct 0 _
      have hc : instOuter LAct [bnum b] row_zeroMul_c = mulFact 0 b := by
        rw [(inst_zeroMul hxb).2, mulFact_zero_left]; rfl
      have hes : ∀ e ∈ [bnum b], IsSemiterm LAct 0 e ∧ termLen LAct e ≤ 12 * ‖0 * b + 0 + b‖ + 3 := by
        simp only [List.mem_singleton, forall_eq]
        exact ⟨hxb, termLen_bnum_le_E' (le_mulS_right 0 b) le_rfl⟩
      have hpf := step0_proof hr0 [bnum b] rfl (fun e he ↦ (hes e he).1) (isFormula_mulFact 0 b) (inst_zeroMul hxb).1 hc
      have hlen := dlen_step0_le hr0 [bnum b] rfl hes one_le_addE hB (isFormula_mulFact 0 b) (inst_zeroMul hxb).1 hc
        (by norm_num) (by simp [row_zeroMul_as]) (formulaLen_mulFact_le hPeq le_rfl)
      rw [cast_rZeroMul] at hpf hlen
      refine ⟨hpf, ?_⟩
      unfold mulEqBound mulNodeCap
      exact le_trans hlen (le_trans le_self_add (le_mul_of_one_le_left zero_le le_add_self))
    · have ha : 1 ≤ a := by
        have := lt_iff_succ_le.mp (pos_iff_ne_zero.mpr ha0); rwa [zero_add] at this
      obtain ⟨hm, hlt, he | ho⟩ := two_le_cases h2
      · -- the even bit
        rw [he] at hd ⊢
        obtain ⟨d', hd', rfl⟩ := (MulGraph.two_mul_iff ha hm).mp hd
        obtain ⟨hpf', hlen'⟩ := ih (b / 2) hlt d' hd'
        set m := b / 2 with hm_def
        have hxm : IsSemiterm LAct 0 (bnum m) := isSemiterm_bnum_LAct 0 _
        have hxam : IsSemiterm LAct 0 (bnum (a * m)) := isSemiterm_bnum_LAct 0 _
        have hmb : m ≤ 2 * m := le_of_lt (Bnum.lt_two_mul hm)
        have hsS : a * m + a + m ≤ a * (2 * m) + a + 2 * m := mulS_mono_right hmb
        have hE : 12 * ‖a * m + a + m‖ + 3 ≤ 12 * ‖a * (2 * m) + a + 2 * m‖ + 3 := mulE_mono hsS
        have hes : ∀ e ∈ [bnum a, bnum m, bnum (a * m)],
            IsSemiterm LAct 0 e ∧ termLen LAct e ≤ 12 * ‖a * (2 * m) + a + 2 * m‖ + 3 := by
          intro e he
          simp only [List.mem_cons, List.mem_singleton, List.not_mem_nil, or_false] at he
          rcases he with rfl | rfl | rfl
          · exact ⟨hxa, termLen_bnum_le_E' (le_mulS_left _ _) le_rfl⟩
          · exact ⟨hxm, termLen_bnum_le_E' (le_trans hmb (le_mulS_right _ _)) le_rfl⟩
          · exact ⟨hxam, termLen_bnum_le_E' (le_trans (mul_le_mulS a m) hsS) le_rfl⟩
        set ps : List (V × V) := [(mulFact a m, d')] with hps_def
        have hps : ∀ p ∈ ps, IsFormula LAct p.1 ∧ DerivationOf TAct p.2 (sing p.1) := by
          intro p hp
          simp only [hps_def, List.mem_singleton] at hp
          subst hp; exact ⟨isFormula_mulFact a m, hpf'⟩
        have hmap : row_twoMulMulS_as.map (instOuter LAct [bnum a, bnum m, bnum (a * m)]) = ps.map Prod.fst := by
          rw [(inst_twoMulMulS hxa hxm hxam).1]
          simp only [hps_def, List.map_cons, List.map_nil, mulFact, eqFactB_eq_eqFact']
        have hc : instOuter LAct [bnum a, bnum m, bnum (a * m)] row_twoMulMulS_c = mulFact a (2 * m) := by
          rw [(inst_twoMulMulS hxa hxm hxam).2, mulFact_two_mul ha hm]; rfl
        have hpsP : ∀ p ∈ ps, formulaLen LAct p.1 ≤ B' * (12 * ‖a * (2 * m) + a + 2 * m‖ + 3) := by
          intro p hp
          simp only [hps_def, List.mem_singleton] at hp
          subst hp; exact formulaLen_mulFact_le hPeq hE
        rw [← stepL_one]
        have hpf := stepL_proof hr3 ps [bnum a, bnum m, bnum (a * m)] rfl (fun e he ↦ (hes e he).1)
          (isFormula_mulFact _ _) hps hmap hc
        have hlen := dlen_stepL_le hr3 ps [bnum a, bnum m, bnum (a * m)] rfl hes one_le_addE hB
          (isFormula_mulFact _ _) hps hmap hc (by norm_num) (by simp [row_twoMulMulS_as])
          (formulaLen_mulFact_le hPeq le_rfl) hpsP
        rw [cast_rTwoMulMul] at hpf hlen
        refine ⟨hpf, ?_⟩
        have h1 : dlen TAct d' ≤ (‖m‖ + 1) * mulNodeCap N B N' B' (a * (2 * m) + a + 2 * m) := by
          unfold mulEqBound at hlen'
          exact le_trans hlen' (mul_le_mul_of_nonneg_left (mulNodeCap_mono hsS) zero_le)
        unfold mulEqBound
        calc dlen TAct (stepL tblM 3 ps (vecOf [bnum a, bnum m, bnum (a * m)]) (mulFact a (2 * m)))
            ≤ factsDlen ps + nodeCost N' B' (12 * ‖a * (2 * m) + a + 2 * m‖ + 3) := hlen
          _ = dlen TAct d' + nodeCost N' B' (12 * ‖a * (2 * m) + a + 2 * m‖ + 3) := by
              simp only [hps_def, factsDlen_cons, factsDlen_nil]; ring
          _ ≤ (‖m‖ + 1) * mulNodeCap N B N' B' (a * (2 * m) + a + 2 * m)
              + mulNodeCap N B N' B' (a * (2 * m) + a + 2 * m) := by
              refine add_le_add h1 ?_
              unfold mulNodeCap; exact le_self_add
          _ = (‖2 * m‖ + 1) * mulNodeCap N B N' B' (a * (2 * m) + a + 2 * m) := by
              rw [length_two_mul_of_pos (lt_of_lt_of_le _root_.zero_lt_one hm)]; ring
      · -- the odd bit
        rw [ho] at hd ⊢
        obtain ⟨d', hd', rfl⟩ := (MulGraph.two_mul_add_one_iff ha hm).mp hd
        obtain ⟨hpf', hlen'⟩ := ih (b / 2) hlt d' hd'
        set m := b / 2 with hm_def
        have hxm : IsSemiterm LAct 0 (bnum m) := isSemiterm_bnum_LAct 0 _
        have hxam : IsSemiterm LAct 0 (bnum (a * m)) := isSemiterm_bnum_LAct 0 _
        have hxab : IsSemiterm LAct 0 (bnum (a * (2 * m + 1))) := isSemiterm_bnum_LAct 0 _
        have hmb : m ≤ 2 * m + 1 := le_of_lt (Bnum.lt_two_mul_add_one hm)
        have hsS : a * m + a + m ≤ a * (2 * m + 1) + a + (2 * m + 1) := mulS_mono_right hmb
        have hE : 12 * ‖a * m + a + m‖ + 3 ≤ 12 * ‖a * (2 * m + 1) + a + (2 * m + 1)‖ + 3 := mulE_mono hsS
        have hab : 2 * (a * m) + a ≤ a * (2 * m + 1) + a + (2 * m + 1) := by
          rw [show 2 * (a * m) + a = a * (2 * m + 1) by ring]; exact mul_le_mulS _ _
        have hes : ∀ e ∈ [bnum a, bnum m, bnum (a * m), bnum (a * (2 * m + 1))],
            IsSemiterm LAct 0 e ∧ termLen LAct e ≤ 12 * ‖a * (2 * m + 1) + a + (2 * m + 1)‖ + 3 := by
          intro e he
          simp only [List.mem_cons, List.mem_singleton, List.not_mem_nil, or_false] at he
          rcases he with rfl | rfl | rfl | rfl
          · exact ⟨hxa, termLen_bnum_le_E' (le_mulS_left _ _) le_rfl⟩
          · exact ⟨hxm, termLen_bnum_le_E' (le_trans hmb (le_mulS_right _ _)) le_rfl⟩
          · exact ⟨hxam, termLen_bnum_le_E' (le_trans (mul_le_mulS a m) hsS) le_rfl⟩
          · exact ⟨hxab, termLen_bnum_le_E' (mul_le_mulS _ _) le_rfl⟩
        set ps : List (V × V) := [(mulFact a m, d'), (addFact (2 * (a * m)) a, addCode tbl (2 * (a * m)) a)] with hps_def
        have hps : ∀ p ∈ ps, IsFormula LAct p.1 ∧ DerivationOf TAct p.2 (sing p.1) := by
          intro p hp
          simp only [hps_def, List.mem_cons, List.mem_singleton, List.not_mem_nil, or_false] at hp
          rcases hp with rfl | rfl
          · exact ⟨isFormula_mulFact a m, hpf'⟩
          · exact ⟨isFormula_addFact _ _, addCode_proof htbl _ _⟩
        have hmap : row_twoMulOneMulS_as.map (instOuter LAct [bnum a, bnum m, bnum (a * m), bnum (a * (2 * m + 1))])
            = ps.map Prod.fst := by
          rw [(inst_twoMulOneMulS hxa hxm hxam hxab).1]
          simp only [hps_def, List.map_cons, List.map_nil, mulFact, eqFactB_eq_eqFact', addFact_two_mul_mul ha hm]
        have hc : instOuter LAct [bnum a, bnum m, bnum (a * m), bnum (a * (2 * m + 1))] row_twoMulOneMulS_c
            = mulFact a (2 * m + 1) := by
          rw [(inst_twoMulOneMulS hxa hxm hxam hxab).2, mulFact_two_mul_add_one hm]; rfl
        have hpsP : ∀ p ∈ ps, formulaLen LAct p.1 ≤ B' * (12 * ‖a * (2 * m + 1) + a + (2 * m + 1)‖ + 3) := by
          intro p hp
          simp only [hps_def, List.mem_cons, List.mem_singleton, List.not_mem_nil, or_false] at hp
          rcases hp with rfl | rfl
          · exact formulaLen_mulFact_le hPeq hE
          · exact formulaLen_addFact_le hPeq (mulE_mono hab)
        rw [← stepL_two]
        have hpf := stepL_proof hr4 ps [bnum a, bnum m, bnum (a * m), bnum (a * (2 * m + 1))] rfl
          (fun e he ↦ (hes e he).1) (isFormula_mulFact _ _) hps hmap hc
        have hlen := dlen_stepL_le hr4 ps [bnum a, bnum m, bnum (a * m), bnum (a * (2 * m + 1))] rfl hes one_le_addE hB
          (isFormula_mulFact _ _) hps hmap hc (by norm_num) (by simp [row_twoMulOneMulS_as])
          (formulaLen_mulFact_le hPeq le_rfl) hpsP
        rw [cast_rTwoMulOneMul] at hpf hlen
        refine ⟨hpf, ?_⟩
        have h1 : dlen TAct d' ≤ (‖m‖ + 1) * mulNodeCap N B N' B' (a * (2 * m + 1) + a + (2 * m + 1)) := by
          unfold mulEqBound at hlen'
          exact le_trans hlen' (mul_le_mul_of_nonneg_left (mulNodeCap_mono hsS) zero_le)
        have h2 := dlen_addCode_mul_le htbl (a := a) hm
        unfold mulEqBound
        calc dlen TAct (stepL tblM 4 ps (vecOf [bnum a, bnum m, bnum (a * m), bnum (a * (2 * m + 1))]) (mulFact a (2 * m + 1)))
            ≤ factsDlen ps + nodeCost N' B' (12 * ‖a * (2 * m + 1) + a + (2 * m + 1)‖ + 3) := hlen
          _ = dlen TAct d' + dlen TAct (addCode tbl (2 * (a * m)) a)
              + nodeCost N' B' (12 * ‖a * (2 * m + 1) + a + (2 * m + 1)‖ + 3) := by
              simp only [hps_def, factsDlen_cons, factsDlen_nil]; ring
          _ ≤ (‖m‖ + 1) * mulNodeCap N B N' B' (a * (2 * m + 1) + a + (2 * m + 1))
              + (‖a * (2 * m + 1) + a + (2 * m + 1)‖ + 1) * (‖a * (2 * m + 1) + a + (2 * m + 1)‖ + 2)
                * nodeCost N B (12 * ‖a * (2 * m + 1) + a + (2 * m + 1)‖ + 3)
              + nodeCost N' B' (12 * ‖a * (2 * m + 1) + a + (2 * m + 1)‖ + 3) :=
              add_le_add (add_le_add h1 h2) le_rfl
          _ = (‖2 * m + 1‖ + 1) * mulNodeCap N B N' B' (a * (2 * m + 1) + a + (2 * m + 1)) := by
              unfold mulNodeCap; rw [length_two_mul_add_one]; ring

/-- **`mulEqCode` is a derivation of `{bnum a · bnum b = bnum (a · b)}`**, in every model, over any sound tables. -/
theorem mulEqCode_proof {tbl N B tblM N' B' : V} (htbl : NumTableOK tbl N B) (htblM : MulTableOK tblM N' B') (a b : V) :
    DerivationOf TAct (mulEqCode tblM tbl a b) (sing (mulFact a b)) :=
  (mulGraph_sound htbl htblM a b _ (mulEqCode_graph tblM tbl a b)).1

/-- **`dlen (mulEqCode tblM tbl a b) ≤ (‖b‖ + 1) · mulNodeCap (a·b + a + b)`** — cubic in the bit length. -/
theorem dlen_mulEqCode_le {tbl N B tblM N' B' : V} (htbl : NumTableOK tbl N B) (htblM : MulTableOK tblM N' B') (a b : V) :
    dlen TAct (mulEqCode tblM tbl a b) ≤ mulEqBound N B N' B' a b :=
  (mulGraph_sound htbl htblM a b _ (mulEqCode_graph tblM tbl a b)).2

/-- The `sLemma` step of N4 is applicable … -/
theorem lemmaOK_mulEq {tbl N B tblM N' B' : V} (htbl : NumTableOK tbl N B) (htblM : MulTableOK tblM N' B') (a b : V) :
    LemmaOK (sLemma (mulFact a b) (mulEqCode tblM tbl a b)) :=
  lemmaOK_of (isFormula_mulFact a b) (mulEqCode_proof htbl htblM a b)

/-- … and its cost: `≤ mulEqBound + 2|Γ| + 2|mulFact a b| + 2`. -/
theorem stepCost_lemma_mulEq {tbl N B tblM N' B' N'' E Γ : V} (htbl : NumTableOK tbl N B) (htblM : MulTableOK tblM N' B') (a b : V) :
    stepCost N'' E Γ (sLemma (mulFact a b) (mulEqCode tblM tbl a b)) ≤
      mulEqBound N B N' B' a b + 2 * setLen LAct Γ + 2 * formulaLen LAct (mulFact a b) + 2 := by
  rw [stepCost_sLemma]
  exact add_le_add (add_le_add (add_le_add (dlen_mulEqCode_le htbl htblM a b) le_rfl) le_rfl) le_rfl

end mulSound

end ArithS
