import ArithS.Necessitation.NumSteps
import ArithS.Necessitation.RowInstB

/-!
# ArithS.Necessitation.NumLength — N5: the closed length fact `‖k‖ = length (k)` as a derivation code

`M4_BOUNDED_HBL/DESIGN_fragments.md` §2.4 (row N5) and §7 step 8: the top of the verification
proof needs the CLOSED fact `lengthFact (bnum ‖k‖) (bnum k)` (`bnum ‖k‖ = ‖bnum k‖` read through
Foundation's `lengthDef` graph) as ONE `sLemma` step. This file is the Σ₁ prover of that fact —
`NumSteps.lean`'s `succCode` pattern (a `Fixpoint` on `⟪z, d⟫`, bit recursion, existence by Σ₁
order induction, uniqueness by Π₁ order induction, `Classical.choose!`), over its OWN four-row
table (`LenTableOK`: `lengthZero`, `lengthOne` — the Frag rows of `Lib/Frag.lean`/`RowInstB.lean`
reused — and the two COMBINED bit rows `lenTwoMulS`/`lenTwoMulOneS`) plus `NumSteps`'s numeral
table (`ltCode` for the `0 < x` antecedent, `succCode` for the successor of the length numeral).

**Why the bit rows carry the successor.** `‖2m‖ = ‖m‖ + 1`, but the CODE `bnum (‖m‖ + 1)` is a
binary numeral, not `bnum ‖m‖ ^+ 𝟏` — the Frag row `lengthTwoMul` (`l = ‖x‖ → l + 1 = ‖2x‖`)
concludes the fact at `bnum ‖m‖ ^+ 𝟏`, one successor step away from the target. The combined row
`l = ‖x‖ → 0 < x → l + 1 = l' → l' = ‖2x‖` takes `succFact ‖m‖ : bnum ‖m‖ + 1 = bnum (‖m‖ + 1)`
as a third cut sub-fact (`succCode`) and concludes at `bnum (‖m‖ + 1)` directly — one Horn use per
bit (`step3` / `step2`), against a new Frag-table row plus three steps per bit a step-list would
need. Hence the `sLemma` route: `lengthEqCode tblL tbl k` with `lengthEqCode_proof`,
`dlen_lengthEqCode_le` (`≤ (‖k‖ + 1) · nodeCap`, `nodeCap` quadratic in `‖k‖` through `ltCode`),
`lemmaOK_lengthEq`, `stepCost_lemma_lengthEq` — the packaging of every other numeral fact.

This is a LEAF file (imports `NumSteps` and `RowInstB`, which `NumSteps` does not import — the
length predicate code `Plength`/`lengthFact` lives there): `NumTableOK` and every existing row
index stay byte-stable.
-/

namespace ArithS

open FFL FFL.FirstOrder Arithmetic Bootstrapping
open PeanoMinus ISigma0 ISigma1
open FFL.FirstOrder.Arithmetic.Bootstrapping.Arithmetic
open LAct

variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

set_option linter.unusedSimpArgs false
set_option linter.unusedSectionVars false

/-! ## 1. The length fact and its Σ₁ graph -/

section lenFact

/-- `RowInstB`'s `eqFactB` is `NumSteps`'s `eqFact` (`PeqB = Peq`). -/
lemma eqFactB_eq_eqFact (a b : V) : eqFactB a b = eqFact a b := rfl

/-- The `length` sentence over `LAct` (`Plength = ⌜lengthS⌝`). -/
noncomputable def lengthS : Semisentence LAct 2 :=
  Semiformula.lMap emb (↑lengthDef : ArithmeticSemisentence 2)
lemma Plength_eq_quote : (Plength : V) = ⌜lengthS⌝ := rfl

noncomputable def lengthFactDef : 𝚺₁.Semisentence 3 := fact2Def lengthS
instance lengthFact_defined : 𝚺₁-Function₂ (lengthFact : V → V → V) via lengthFactDef := fact2_defined lengthS
instance lengthFact_definable : 𝚺₁-Function₂ (lengthFact : V → V → V) := lengthFact_defined.to_definable

/-- **N5's fact**: `lengthEqFact k := lengthFact (bnum ‖k‖) (bnum k)` — `bnum ‖k‖ = ‖bnum k‖`. -/
noncomputable def lengthEqFact (k : V) : V := lengthFact (bnum ‖k‖) (bnum k)
noncomputable def lengthEqFactDef : 𝚺₁.Semisentence 2 := .mkSigma
  “y k. ∃ l, !lengthDef l k ∧ ∃ tl, !bnumGraph tl l ∧ ∃ tk, !bnumGraph tk k ∧ !lengthFactDef y tl tk”
instance lengthEqFact_defined : 𝚺₁-Function₁ (lengthEqFact : V → V) via lengthEqFactDef := .mk fun v ↦ by
  simp [lengthEqFactDef, length_defined.iff, bnum.defined.iff, lengthFact_defined.iff, lengthEqFact]
instance lengthEqFact_definable : 𝚺₁-Function₁ (lengthEqFact : V → V) := lengthEqFact_defined.to_definable

lemma isFormula_lengthEqFact (k : V) : IsFormula LAct (lengthEqFact k) :=
  isFormula_lengthFact (isSemiterm_bnum_LAct 0 _) (isSemiterm_bnum_LAct 0 _)

/-- `|lengthEqFact k| ≤ B·E` once `B ≥ |Plength|` and `E ≥ 12‖k‖ + 3`. -/
lemma formulaLen_lengthEqFact_le {B E k : V} (hP : formulaLen LAct (Plength : V) ≤ B) (hE : 12 * ‖k‖ + 3 ≤ E) :
    formulaLen LAct (lengthEqFact k) ≤ B * E :=
  le_trans (formulaLen_lengthFact_le (le_trans one_le_addE hE) (isSemiterm_bnum_LAct 0 _) (isSemiterm_bnum_LAct 0 _)
    (termLen_bnum_le_E' (length_le k) hE) (termLen_bnum_le_E' le_rfl hE)) (mul_le_mul_of_nonneg_right hP zero_le)

lemma lengthEqFact_zero : lengthEqFact (0 : V) = lengthFact (𝟎 : V) (𝟎 : V) := by
  unfold lengthEqFact; rw [length_zero, bnum_zero]
lemma lengthEqFact_one : lengthEqFact (1 : V) = lengthFact (𝟏 : V) (𝟏 : V) := by
  unfold lengthEqFact; rw [length_one, bnum_one]
lemma lengthEqFact_two_mul {m : V} (hm : 1 ≤ m) :
    lengthEqFact (2 * m) = lengthFact (bnum (‖m‖ + 1)) (((𝟏 : V) ^+ (𝟏 : V)) ^* bnum m) := by
  unfold lengthEqFact
  rw [length_two_mul_of_pos (lt_of_lt_of_le _root_.zero_lt_one hm), bnum_two_mul hm]; rfl
lemma lengthEqFact_two_mul_add_one {m : V} (hm : 1 ≤ m) :
    lengthEqFact (2 * m + 1) = lengthFact (bnum (‖m‖ + 1)) ((((𝟏 : V) ^+ (𝟏 : V)) ^* bnum m) ^+ (𝟏 : V)) := by
  unfold lengthEqFact
  rw [length_two_mul_add_one, bnum_two_mul_add_one hm]; rfl

end lenFact

/-! ## 2. The two combined bit rows (the base rows `lengthZero`/`lengthOne` are the Frag rows) -/

section rows

set_option linter.unusedVariables false

/-- `l = ‖x‖ → 0 < x → l + 1 = l' → l' = ‖2x‖` (N5, the even bit with the successor folded in). -/
noncomputable def lenTwoMulSB : ArithmeticSemisentence 3 :=
  “l' l x. !lengthDef l x → 0 < x → l + 1 = l' → !lengthDef l' (2 * x)”
noncomputable def lenTwoMulS : ArithmeticSentence := ∀¹* lenTwoMulSB
lemma models_lenTwoMulS : V↓[ℒₒᵣ] ⊧ lenTwoMulS ↔
    ∀ l' l x : V, l = ‖x‖ → (0 : V) < x → l + 1 = l' → l' = ‖(2 : V) * x‖ := by
  simp [lenTwoMulS, lenTwoMulSB, models_iff, Matrix.vecForall_iff, length_defined.iff]
theorem pa_proves_lenTwoMulS : 𝗣𝗔 ⊢ lenTwoMulS :=
  Lib.pa_proves_of_models fun _ _ _ ↦ models_lenTwoMulS.mpr fun _ _ _ h₁ h₂ h₃ ↦ by
    subst_vars; exact (length_two_mul_of_pos h₂).symm
theorem lib_lenTwoMulS : Lib lenTwoMulS := Lib.of_pa pa_proves_lenTwoMulS

noncomputable def row_lenTwoMulS_as : List V :=
  [subst LAct (listToVec [bv 1, bv 2]) Plength, subst LAct (listToVec [(𝟎 : V), bv 2]) Plt,
   subst LAct (listToVec [bv 1 ^+ (𝟏 : V), bv 0]) PeqB]
noncomputable def row_lenTwoMulS_c : V := subst LAct (listToVec [bv 0, ((𝟏 : V) ^+ (𝟏 : V)) ^* bv 2]) Plength

theorem quote_row_lenTwoMulS : (⌜Semiformula.lMap emb lenTwoMulSB⌝ : V) = impChain LAct row_lenTwoMulS_as row_lenTwoMulS_c := by
  unfold lenTwoMulSB row_lenTwoMulS_as row_lenTwoMulS_c Plength Plt PeqB
  all_goals row_shapeB

/-- `lenTwoMulS` at the witnesses `[wx, wl, wl']` (the DSL variables right-to-left). -/
lemma inst_lenTwoMulS {wx wl wl' : V} (hwx : IsSemiterm LAct 0 wx) (hwl : IsSemiterm LAct 0 wl) (hwl' : IsSemiterm LAct 0 wl') :
    row_lenTwoMulS_as.map (instOuter LAct [wx, wl, wl']) = [lengthFact wl wx, ltFact (𝟎 : V) wx, eqFactB (wl ^+ (𝟏 : V)) wl'] ∧
    instOuter LAct [wx, wl, wl'] row_lenTwoMulS_c = lengthFact wl' (((𝟏 : V) ^+ (𝟏 : V)) ^* wx) := by
  have hes : ∀ e ∈ ([wx, wl, wl'] : List V), IsSemiterm LAct 0 e :=
    (List.forall_mem_cons.mpr ⟨hwx, List.forall_mem_cons.mpr ⟨hwl, List.forall_mem_cons.mpr ⟨hwl', List.forall_mem_nil _⟩⟩⟩)
  unfold row_lenTwoMulS_as row_lenTwoMulS_c
  simp only [List.map_cons, List.map_nil]
  rw [instOuter_subst_listToVec _ isSemiformula_Plength (by rfl) _ hes (by row_entriesB),
    instOuter_subst_listToVec _ isSemiformula_Plt (by rfl) _ hes (by row_entriesB),
    instOuter_subst_listToVec _ isSemiformula_PeqB (by rfl) _ hes (by row_entriesB),
    instOuter_subst_listToVec _ isSemiformula_Plength (by rfl) _ hes (by row_entriesB)]
  all_goals try row_entries_simpB
  row_finish

/-- `l = ‖x‖ → l + 1 = l' → l' = ‖2x + 1‖` (N5, the odd bit with the successor folded in). -/
noncomputable def lenTwoMulOneSB : ArithmeticSemisentence 3 :=
  “l' l x. !lengthDef l x → l + 1 = l' → !lengthDef l' (2 * x + 1)”
noncomputable def lenTwoMulOneS : ArithmeticSentence := ∀¹* lenTwoMulOneSB
lemma models_lenTwoMulOneS : V↓[ℒₒᵣ] ⊧ lenTwoMulOneS ↔
    ∀ l' l x : V, l = ‖x‖ → l + 1 = l' → l' = ‖(2 : V) * x + 1‖ := by
  simp [lenTwoMulOneS, lenTwoMulOneSB, models_iff, Matrix.vecForall_iff, length_defined.iff]
theorem pa_proves_lenTwoMulOneS : 𝗣𝗔 ⊢ lenTwoMulOneS :=
  Lib.pa_proves_of_models fun _ _ _ ↦ models_lenTwoMulOneS.mpr fun _ _ _ h₁ h₂ ↦ by
    subst_vars; exact (length_two_mul_add_one _).symm
theorem lib_lenTwoMulOneS : Lib lenTwoMulOneS := Lib.of_pa pa_proves_lenTwoMulOneS

noncomputable def row_lenTwoMulOneS_as : List V :=
  [subst LAct (listToVec [bv 1, bv 2]) Plength, subst LAct (listToVec [bv 1 ^+ (𝟏 : V), bv 0]) PeqB]
noncomputable def row_lenTwoMulOneS_c : V :=
  subst LAct (listToVec [bv 0, (((𝟏 : V) ^+ (𝟏 : V)) ^* bv 2) ^+ (𝟏 : V)]) Plength

theorem quote_row_lenTwoMulOneS : (⌜Semiformula.lMap emb lenTwoMulOneSB⌝ : V) = impChain LAct row_lenTwoMulOneS_as row_lenTwoMulOneS_c := by
  unfold lenTwoMulOneSB row_lenTwoMulOneS_as row_lenTwoMulOneS_c Plength PeqB
  all_goals row_shapeB

/-- `lenTwoMulOneS` at the witnesses `[wx, wl, wl']`. -/
lemma inst_lenTwoMulOneS {wx wl wl' : V} (hwx : IsSemiterm LAct 0 wx) (hwl : IsSemiterm LAct 0 wl) (hwl' : IsSemiterm LAct 0 wl') :
    row_lenTwoMulOneS_as.map (instOuter LAct [wx, wl, wl']) = [lengthFact wl wx, eqFactB (wl ^+ (𝟏 : V)) wl'] ∧
    instOuter LAct [wx, wl, wl'] row_lenTwoMulOneS_c = lengthFact wl' ((((𝟏 : V) ^+ (𝟏 : V)) ^* wx) ^+ (𝟏 : V)) := by
  have hes : ∀ e ∈ ([wx, wl, wl'] : List V), IsSemiterm LAct 0 e :=
    (List.forall_mem_cons.mpr ⟨hwx, List.forall_mem_cons.mpr ⟨hwl, List.forall_mem_cons.mpr ⟨hwl', List.forall_mem_nil _⟩⟩⟩)
  unfold row_lenTwoMulOneS_as row_lenTwoMulOneS_c
  simp only [List.map_cons, List.map_nil]
  rw [instOuter_subst_listToVec _ isSemiformula_Plength (by rfl) _ hes (by row_entriesB),
    instOuter_subst_listToVec _ isSemiformula_PeqB (by rfl) _ hes (by row_entriesB),
    instOuter_subst_listToVec _ isSemiformula_Plength (by rfl) _ hes (by row_entriesB)]
  all_goals try row_entries_simpB
  row_finish

end rows

/-! ## 3. The length table: four rows, in every model -/

section table

def rLenZero : ℕ := 0
def rLenOne : ℕ := 1
def rLenTwoMul : ℕ := 2
def rLenTwoMulOne : ℕ := 3

lemma cast_rLenZero : ((rLenZero : ℕ) : V) = 0 := by simp [rLenZero]
lemma cast_rLenOne : ((rLenOne : ℕ) : V) = 1 := by simp [rLenOne]
lemma cast_rLenTwoMul : ((rLenTwoMul : ℕ) : V) = 2 := by simp [rLenTwoMul]
lemma cast_rLenTwoMulOne : ((rLenTwoMulOne : ℕ) : V) = 3 := by simp [rLenTwoMulOne]

/-- **The length table is sound**: the four rows plus the bounds on the predicate codes. -/
def LenTableOK (tbl N B : V) : Prop :=
  NumRowOK tbl rLenZero N B 1 row_lengthZero_as row_lengthZero_c ∧
  NumRowOK tbl rLenOne N B 1 row_lengthOne_as row_lengthOne_c ∧
  NumRowOK tbl rLenTwoMul N B 3 row_lenTwoMulS_as row_lenTwoMulS_c ∧
  NumRowOK tbl rLenTwoMulOne N B 3 row_lenTwoMulOneS_as row_lenTwoMulOneS_c ∧
  formulaLen LAct (Plength : V) ≤ B ∧
  formulaLen LAct (Peq : V) ≤ B ∧
  formulaLen LAct (Plt : V) ≤ B ∧
  1 ≤ B

/-- **A length table exists in every model**, with ONE standard pair of bounds. -/
theorem exists_lenTable : ∃ N B : ℕ, ∀ (V : Type) [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁],
    ∃ tbl : V, LenTableOK tbl (N : V) (B : V) := by
  obtain ⟨N0, h0⟩ := (lib_lengthZero).univ_code
  obtain ⟨N1, h1⟩ := (lib_lengthOne).univ_code
  obtain ⟨N2, h2⟩ := (lib_lenTwoMulS).univ_code
  obtain ⟨N3, h3⟩ := (lib_lenTwoMulOneS).univ_code
  refine ⟨N0 + N1 + N2 + N3, rowLen lengthZeroB + rowLen lengthOneB + rowLen lenTwoMulSB + rowLen lenTwoMulOneSB
    + flen (Rewriting.emb lengthS : Semiproposition LAct 2) + flen (Rewriting.emb eqS : Semiproposition LAct 2)
    + flen (Rewriting.emb ltS : Semiproposition LAct 2) + 1, fun V _ _ ↦ ?_⟩
  obtain ⟨d0, hd0, hl0⟩ := h0 V
  obtain ⟨d1, hd1, hl1⟩ := h1 V
  obtain ⟨d2, hd2, hl2⟩ := h2 V
  obtain ⟨d3, hd3, hl3⟩ := h3 V
  refine ⟨vecOf [⟪d0, vecOf row_lengthZero_as, row_lengthZero_c⟫, ⟪d1, vecOf row_lengthOne_as, row_lengthOne_c⟫,
    ⟪d2, vecOf row_lenTwoMulS_as, row_lenTwoMulS_c⟫, ⟪d3, vecOf row_lenTwoMulOneS_as, row_lenTwoMulOneS_c⟫], ?_⟩
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact numRowOK_of lengthZeroB (by unfold rLenZero; rw [nth_vecOf _ 0 (by simp)]; rfl) quote_row_lengthZero hd0
      (le_trans hl0 (by exact_mod_cast (by omega : N0 ≤ N0 + N1 + N2 + N3)))
      (by exact_mod_cast (by omega : rowLen lengthZeroB ≤ rowLen lengthZeroB + rowLen lengthOneB + rowLen lenTwoMulSB + rowLen lenTwoMulOneSB + flen (Rewriting.emb lengthS : Semiproposition LAct 2) + flen (Rewriting.emb eqS : Semiproposition LAct 2) + flen (Rewriting.emb ltS : Semiproposition LAct 2) + 1))
  · exact numRowOK_of lengthOneB (by unfold rLenOne; rw [nth_vecOf _ 1 (by simp)]; rfl) quote_row_lengthOne hd1
      (le_trans hl1 (by exact_mod_cast (by omega : N1 ≤ N0 + N1 + N2 + N3)))
      (by exact_mod_cast (by omega : rowLen lengthOneB ≤ rowLen lengthZeroB + rowLen lengthOneB + rowLen lenTwoMulSB + rowLen lenTwoMulOneSB + flen (Rewriting.emb lengthS : Semiproposition LAct 2) + flen (Rewriting.emb eqS : Semiproposition LAct 2) + flen (Rewriting.emb ltS : Semiproposition LAct 2) + 1))
  · exact numRowOK_of lenTwoMulSB (by unfold rLenTwoMul; rw [nth_vecOf _ 2 (by simp)]; rfl) quote_row_lenTwoMulS hd2
      (le_trans hl2 (by exact_mod_cast (by omega : N2 ≤ N0 + N1 + N2 + N3)))
      (by exact_mod_cast (by omega : rowLen lenTwoMulSB ≤ rowLen lengthZeroB + rowLen lengthOneB + rowLen lenTwoMulSB + rowLen lenTwoMulOneSB + flen (Rewriting.emb lengthS : Semiproposition LAct 2) + flen (Rewriting.emb eqS : Semiproposition LAct 2) + flen (Rewriting.emb ltS : Semiproposition LAct 2) + 1))
  · exact numRowOK_of lenTwoMulOneSB (by unfold rLenTwoMulOne; rw [nth_vecOf _ 3 (by simp)]; rfl) quote_row_lenTwoMulOneS hd3
      (le_trans hl3 (by exact_mod_cast (by omega : N3 ≤ N0 + N1 + N2 + N3)))
      (by exact_mod_cast (by omega : rowLen lenTwoMulOneSB ≤ rowLen lengthZeroB + rowLen lengthOneB + rowLen lenTwoMulSB + rowLen lenTwoMulOneSB + flen (Rewriting.emb lengthS : Semiproposition LAct 2) + flen (Rewriting.emb eqS : Semiproposition LAct 2) + flen (Rewriting.emb ltS : Semiproposition LAct 2) + 1))
  · rw [Plength_eq_quote, formulaLen_quote_semisentence_V']
    exact_mod_cast (by omega : flen (Rewriting.emb lengthS : Semiproposition LAct 2) ≤ rowLen lengthZeroB + rowLen lengthOneB + rowLen lenTwoMulSB + rowLen lenTwoMulOneSB + flen (Rewriting.emb lengthS : Semiproposition LAct 2) + flen (Rewriting.emb eqS : Semiproposition LAct 2) + flen (Rewriting.emb ltS : Semiproposition LAct 2) + 1)
  · rw [Peq, formulaLen_quote_semisentence_V']
    exact_mod_cast (by omega : flen (Rewriting.emb eqS : Semiproposition LAct 2) ≤ rowLen lengthZeroB + rowLen lengthOneB + rowLen lenTwoMulSB + rowLen lenTwoMulOneSB + flen (Rewriting.emb lengthS : Semiproposition LAct 2) + flen (Rewriting.emb eqS : Semiproposition LAct 2) + flen (Rewriting.emb ltS : Semiproposition LAct 2) + 1)
  · rw [Plt_eq_quote, formulaLen_quote_semisentence_V']
    exact_mod_cast (by omega : flen (Rewriting.emb ltS : Semiproposition LAct 2) ≤ rowLen lengthZeroB + rowLen lengthOneB + rowLen lenTwoMulSB + rowLen lenTwoMulOneSB + flen (Rewriting.emb lengthS : Semiproposition LAct 2) + flen (Rewriting.emb eqS : Semiproposition LAct 2) + flen (Rewriting.emb ltS : Semiproposition LAct 2) + 1)
  · exact_mod_cast (by omega : 1 ≤ rowLen lengthZeroB + rowLen lengthOneB + rowLen lenTwoMulSB + rowLen lenTwoMulOneSB + flen (Rewriting.emb lengthS : Semiproposition LAct 2) + flen (Rewriting.emb eqS : Semiproposition LAct 2) + flen (Rewriting.emb ltS : Semiproposition LAct 2) + 1)

end table


/-! ## 4. The bit recursion: `LenGraph tblL tbl z d` (a `Fixpoint` on `⟪z, d⟫`, two table parameters)

`z = 0` by `lengthZero`, `z = 1` by `lengthOne` (a dummy witness `bnum 0`), `z = 2m` by `lenTwoMulS` at
`[bnum m, bnum ‖m‖, bnum (‖m‖ + 1)]` from the fact for `m`, `ltCode tbl 0 m` and `succCode tbl ‖m‖`
(`step3`), `z = 2m + 1` by `lenTwoMulOneS` from the fact for `m` and `succCode tbl ‖m‖` (`step2`). -/

section lenGraph

lemma d_lt_step3 (tbl i F₁ d₁ F₂ d₂ F₃ d₃ ev A : V) : d₁ < step3 tbl i F₁ d₁ F₂ d₂ F₃ d₃ ev A :=
  lt_trans (d_lt_wkRule _ _) (d₁_lt_cutRule _ _ _ _)

namespace LenG

/-- The graph: `⟪z, d⟫` where `d` is the length-fact derivation of `z`. -/
def Phi (tblL tbl : V) (C : Set V) (pr : V) : Prop :=
  ∃ z d, pr = ⟪z, d⟫ ∧
  ( (z = 0 ∧ d = step0 tblL 0 (vecOf [bnum 0]) (lengthEqFact 0)) ∨
    (z = 1 ∧ d = step0 tblL 1 (vecOf [bnum 0]) (lengthEqFact 1)) ∨
    (∃ m d', 1 ≤ m ∧ z = 2 * m ∧ ⟪m, d'⟫ ∈ C ∧
      d = step3 tblL 2 (lengthEqFact m) d' (ltFact (bnum 0) (bnum m)) (ltCode tbl 0 m) (succFact ‖m‖) (succCode tbl ‖m‖)
            (vecOf [bnum m, bnum ‖m‖, bnum (‖m‖ + 1)]) (lengthEqFact z)) ∨
    (∃ m d', 1 ≤ m ∧ z = 2 * m + 1 ∧ ⟪m, d'⟫ ∈ C ∧
      d = step2 tblL 3 (lengthEqFact m) d' (succFact ‖m‖) (succCode tbl ‖m‖)
            (vecOf [bnum m, bnum ‖m‖, bnum (‖m‖ + 1)]) (lengthEqFact z)) )

noncomputable def blueprint : Fixpoint.Blueprint 2 := ⟨.mkDelta
  (.mkSigma “pr C tblL tbl.
    ∃ z <⁺ pr, ∃ d <⁺ pr, !pairDef pr z d ∧
    ( (z = 0 ∧ ∃ t0, !bnumGraph t0 0 ∧ ∃ ev, !adjoinDef ev t0 0 ∧ ∃ A, !lengthEqFactDef A 0 ∧
        ∃ x, !step0Def x tblL 0 ev A ∧ d = x) ∨
      (z = 1 ∧ ∃ t0, !bnumGraph t0 0 ∧ ∃ ev, !adjoinDef ev t0 0 ∧ ∃ A, !lengthEqFactDef A 1 ∧
        ∃ x, !step0Def x tblL 1 ev A ∧ d = x) ∨
      (∃ m < z, ∃ d' < d, 1 ≤ m ∧ z = 2 * m ∧ :⟪m, d'⟫:∈ C ∧
        ∃ F, !lengthEqFactDef F m ∧ ∃ t0, !bnumGraph t0 0 ∧ ∃ tm, !bnumGraph tm m ∧ ∃ G, !ltFactDef G t0 tm ∧
        ∃ dG, !ltCodeDef dG tbl 0 m ∧ ∃ l, !lengthDef l m ∧ ∃ H, !succFactDef H l ∧ ∃ dH, !succCodeDef dH tbl l ∧
        ∃ tl, !bnumGraph tl l ∧ ∃ tl1, !bnumGraph tl1 (l + 1) ∧
        ∃ v0, !adjoinDef v0 tl1 0 ∧ ∃ v1, !adjoinDef v1 tl v0 ∧ ∃ ev, !adjoinDef ev tm v1 ∧
        ∃ A, !lengthEqFactDef A z ∧ ∃ x, !step3Def x tblL 2 F d' G dG H dH ev A ∧ d = x) ∨
      (∃ m < z, ∃ d' < d, 1 ≤ m ∧ z = 2 * m + 1 ∧ :⟪m, d'⟫:∈ C ∧
        ∃ F, !lengthEqFactDef F m ∧ ∃ l, !lengthDef l m ∧ ∃ H, !succFactDef H l ∧ ∃ dH, !succCodeDef dH tbl l ∧
        ∃ tm, !bnumGraph tm m ∧ ∃ tl, !bnumGraph tl l ∧ ∃ tl1, !bnumGraph tl1 (l + 1) ∧
        ∃ v0, !adjoinDef v0 tl1 0 ∧ ∃ v1, !adjoinDef v1 tl v0 ∧ ∃ ev, !adjoinDef ev tm v1 ∧
        ∃ A, !lengthEqFactDef A z ∧ ∃ x, !step2Def x tblL 3 F d' H dH ev A ∧ d = x) )”)
  (.mkPi “pr C tblL tbl.
    ∃ z <⁺ pr, ∃ d <⁺ pr, !pairDef pr z d ∧
    ( (z = 0 ∧ ∀ t0, !bnumGraph t0 0 → ∀ ev, !adjoinDef ev t0 0 → ∀ A, !lengthEqFactDef A 0 →
        ∀ x, !step0Def x tblL 0 ev A → d = x) ∨
      (z = 1 ∧ ∀ t0, !bnumGraph t0 0 → ∀ ev, !adjoinDef ev t0 0 → ∀ A, !lengthEqFactDef A 1 →
        ∀ x, !step0Def x tblL 1 ev A → d = x) ∨
      (∃ m < z, ∃ d' < d, 1 ≤ m ∧ z = 2 * m ∧ :⟪m, d'⟫:∈ C ∧
        ∀ F, !lengthEqFactDef F m → ∀ t0, !bnumGraph t0 0 → ∀ tm, !bnumGraph tm m → ∀ G, !ltFactDef G t0 tm →
        ∀ dG, !ltCodeDef dG tbl 0 m → ∀ l, !lengthDef l m → ∀ H, !succFactDef H l → ∀ dH, !succCodeDef dH tbl l →
        ∀ tl, !bnumGraph tl l → ∀ tl1, !bnumGraph tl1 (l + 1) →
        ∀ v0, !adjoinDef v0 tl1 0 → ∀ v1, !adjoinDef v1 tl v0 → ∀ ev, !adjoinDef ev tm v1 →
        ∀ A, !lengthEqFactDef A z → ∀ x, !step3Def x tblL 2 F d' G dG H dH ev A → d = x) ∨
      (∃ m < z, ∃ d' < d, 1 ≤ m ∧ z = 2 * m + 1 ∧ :⟪m, d'⟫:∈ C ∧
        ∀ F, !lengthEqFactDef F m → ∀ l, !lengthDef l m → ∀ H, !succFactDef H l → ∀ dH, !succCodeDef dH tbl l →
        ∀ tm, !bnumGraph tm m → ∀ tl, !bnumGraph tl l → ∀ tl1, !bnumGraph tl1 (l + 1) →
        ∀ v0, !adjoinDef v0 tl1 0 → ∀ v1, !adjoinDef v1 tl v0 → ∀ ev, !adjoinDef ev tm v1 →
        ∀ A, !lengthEqFactDef A z → ∀ x, !step2Def x tblL 3 F d' H dH ev A → d = x) )”)⟩

/-- `Phi` with the bounds the blueprint carries. -/
private lemma phi_iff (tblL tbl C pr : V) :
    Phi tblL tbl {x | x ∈ C} pr ↔
    ∃ z ≤ pr, ∃ d ≤ pr, pr = ⟪z, d⟫ ∧
    ( (z = 0 ∧ d = step0 tblL 0 (vecOf [bnum 0]) (lengthEqFact 0)) ∨
      (z = 1 ∧ d = step0 tblL 1 (vecOf [bnum 0]) (lengthEqFact 1)) ∨
      (∃ m < z, ∃ d' < d, 1 ≤ m ∧ z = 2 * m ∧ ⟪m, d'⟫ ∈ C ∧
        d = step3 tblL 2 (lengthEqFact m) d' (ltFact (bnum 0) (bnum m)) (ltCode tbl 0 m) (succFact ‖m‖) (succCode tbl ‖m‖)
              (vecOf [bnum m, bnum ‖m‖, bnum (‖m‖ + 1)]) (lengthEqFact z)) ∨
      (∃ m < z, ∃ d' < d, 1 ≤ m ∧ z = 2 * m + 1 ∧ ⟪m, d'⟫ ∈ C ∧
        d = step2 tblL 3 (lengthEqFact m) d' (succFact ‖m‖) (succCode tbl ‖m‖)
              (vecOf [bnum m, bnum ‖m‖, bnum (‖m‖ + 1)]) (lengthEqFact z)) ) := by
  constructor
  · rintro ⟨z, d, rfl, h⟩
    refine ⟨z, le_pair_left _ _, d, le_pair_right _ _, rfl, ?_⟩
    rcases h with h | h | ⟨m, d', hm, rfl, hC, rfl⟩ | ⟨m, d', hm, rfl, hC, rfl⟩
    · exact Or.inl h
    · exact Or.inr (Or.inl h)
    · exact Or.inr (Or.inr (Or.inl ⟨m, Bnum.lt_two_mul hm, d', d_lt_step3 _ _ _ _ _ _ _ _ _ _, hm, rfl, hC, rfl⟩))
    · exact Or.inr (Or.inr (Or.inr ⟨m, Bnum.lt_two_mul_add_one hm, d', d_lt_step2 _ _ _ _ _ _ _ _, hm, rfl, hC, rfl⟩))
  · rintro ⟨z, _, d, _, rfl, h⟩
    refine ⟨z, d, rfl, ?_⟩
    rcases h with h | h | ⟨m, _, d', _, hm, rfl, hC, rfl⟩ | ⟨m, _, d', _, hm, rfl, hC, rfl⟩
    · exact Or.inl h
    · exact Or.inr (Or.inl h)
    · exact Or.inr (Or.inr (Or.inl ⟨m, d', hm, rfl, hC, rfl⟩))
    · exact Or.inr (Or.inr (Or.inr ⟨m, d', hm, rfl, hC, rfl⟩))

noncomputable def construction : Fixpoint.Construction V blueprint where
  Φ := fun v ↦ Phi (v 0) (v 1)
  defined := .mk <| by
    constructor
    · intro v
      simp [blueprint, lengthEqFact_defined.iff, bnum.defined.iff, step0_defined.iff, step2_defined.iff,
        step3_defined.iff, ltFact_defined'.iff, ltCode_defined.iff, length_defined.iff, succFact_defined.iff,
        succCode_defined.iff, numeral_eq_natCast]
    · intro v
      symm
      simpa [blueprint, lengthEqFact_defined.iff, bnum.defined.iff, step0_defined.iff, step2_defined.iff,
        step3_defined.iff, ltFact_defined'.iff, ltCode_defined.iff, length_defined.iff, succFact_defined.iff,
        succCode_defined.iff, numeral_eq_natCast] using phi_iff (v 2) (v 3) (v 1) (v 0)
  monotone := by
    rintro C C' hC _ pr ⟨z, d, rfl, h⟩
    refine ⟨z, d, rfl, ?_⟩
    rcases h with h | h | ⟨m, d', hm, rfl, hC', rfl⟩ | ⟨m, d', hm, rfl, hC', rfl⟩
    · exact Or.inl h
    · exact Or.inr (Or.inl h)
    · exact Or.inr (Or.inr (Or.inl ⟨m, d', hm, rfl, hC hC', rfl⟩))
    · exact Or.inr (Or.inr (Or.inr ⟨m, d', hm, rfl, hC hC', rfl⟩))

instance : construction.Finite V where
  finite := by
    rintro C _ pr ⟨z, d, rfl, h⟩
    rcases h with h | h | ⟨m, d', hm, rfl, hC', rfl⟩ | ⟨m, d', hm, rfl, hC', rfl⟩
    · exact ⟨0, z, _, rfl, Or.inl h⟩
    · exact ⟨0, z, _, rfl, Or.inr (Or.inl h)⟩
    · exact ⟨⟪m, d'⟫ + 1, _, _, rfl, Or.inr (Or.inr (Or.inl ⟨m, d', hm, rfl, ⟨hC', lt_add_one _⟩, rfl⟩))⟩
    · exact ⟨⟪m, d'⟫ + 1, _, _, rfl, Or.inr (Or.inr (Or.inr ⟨m, d', hm, rfl, ⟨hC', lt_add_one _⟩, rfl⟩))⟩

end LenG

/-- `LenGraph tblL tbl z d`: `d` is the length-fact derivation of `z` over the tables. -/
def LenGraph (tblL tbl z d : V) : Prop := LenG.construction.Fixpoint ![tblL, tbl] ⟪z, d⟫

noncomputable def lenGraphDef : 𝚺₁.Semisentence 4 := .mkSigma
  “tblL tbl z d. ∃ p, !pairDef p z d ∧ !LenG.blueprint.fixpointDef p tblL tbl”

instance lenGraph_defined : 𝚺₁-Relation₄ (LenGraph : V → V → V → V → Prop) via lenGraphDef := .mk fun v ↦ by
  simp [lenGraphDef, LenG.construction.eval_fixpointDef, LenGraph]
instance lenGraph_definable : 𝚺₁-Relation₄ (LenGraph : V → V → V → V → Prop) := lenGraph_defined.to_definable

lemma LenGraph.case_iff {tblL tbl z d : V} :
    LenGraph tblL tbl z d ↔
    (z = 0 ∧ d = step0 tblL 0 (vecOf [bnum 0]) (lengthEqFact 0)) ∨
    (z = 1 ∧ d = step0 tblL 1 (vecOf [bnum 0]) (lengthEqFact 1)) ∨
    (∃ m d', 1 ≤ m ∧ z = 2 * m ∧ LenGraph tblL tbl m d' ∧
      d = step3 tblL 2 (lengthEqFact m) d' (ltFact (bnum 0) (bnum m)) (ltCode tbl 0 m) (succFact ‖m‖) (succCode tbl ‖m‖)
            (vecOf [bnum m, bnum ‖m‖, bnum (‖m‖ + 1)]) (lengthEqFact z)) ∨
    (∃ m d', 1 ≤ m ∧ z = 2 * m + 1 ∧ LenGraph tblL tbl m d' ∧
      d = step2 tblL 3 (lengthEqFact m) d' (succFact ‖m‖) (succCode tbl ‖m‖)
            (vecOf [bnum m, bnum ‖m‖, bnum (‖m‖ + 1)]) (lengthEqFact z)) :=
  Iff.trans LenG.construction.case (by simp [LenG.construction, LenG.Phi, LenGraph])

lemma LenGraph.zero_iff {tblL tbl d : V} : LenGraph tblL tbl 0 d ↔ d = step0 tblL 0 (vecOf [bnum 0]) (lengthEqFact 0) := by
  rw [LenGraph.case_iff]
  constructor
  · rintro (⟨_, rfl⟩ | ⟨h, _⟩ | ⟨m, _, hm, h, _⟩ | ⟨m, _, hm, h, _⟩)
    · rfl
    · exact absurd h.symm Arithmetic.one_ne_zero
    · exact absurd h.symm (two_mul_ne_zero hm)
    · exact absurd h.symm (two_mul_add_one_ne_zero m)
  · rintro rfl; exact Or.inl ⟨rfl, rfl⟩

lemma LenGraph.one_iff {tblL tbl d : V} : LenGraph tblL tbl 1 d ↔ d = step0 tblL 1 (vecOf [bnum 0]) (lengthEqFact 1) := by
  rw [LenGraph.case_iff]
  constructor
  · rintro (⟨h, _⟩ | ⟨_, rfl⟩ | ⟨m, _, hm, h, _⟩ | ⟨m, _, hm, h, _⟩)
    · exact absurd h Arithmetic.one_ne_zero
    · rfl
    · exact absurd h.symm (two_mul_ne_one m)
    · exact absurd h.symm (two_mul_add_one_ne_one hm)
  · rintro rfl; exact Or.inr (Or.inl ⟨rfl, rfl⟩)

lemma LenGraph.two_mul_iff {tblL tbl m d : V} (hm : 1 ≤ m) :
    LenGraph tblL tbl (2 * m) d ↔ ∃ d', LenGraph tblL tbl m d' ∧
      d = step3 tblL 2 (lengthEqFact m) d' (ltFact (bnum 0) (bnum m)) (ltCode tbl 0 m) (succFact ‖m‖) (succCode tbl ‖m‖)
            (vecOf [bnum m, bnum ‖m‖, bnum (‖m‖ + 1)]) (lengthEqFact (2 * m)) := by
  rw [LenGraph.case_iff]
  constructor
  · rintro (⟨h, _⟩ | ⟨h, _⟩ | ⟨m', d', _, h, hd', rfl⟩ | ⟨m', _, _, h, _⟩)
    · exact absurd h (two_mul_ne_zero hm)
    · exact absurd h (two_mul_ne_one m)
    · obtain rfl := two_mul_inj h; exact ⟨d', hd', rfl⟩
    · exact absurd h (two_mul_ne_two_mul_add_one m m')
  · rintro ⟨d', hd', rfl⟩; exact Or.inr (Or.inr (Or.inl ⟨m, d', hm, rfl, hd', rfl⟩))

lemma LenGraph.two_mul_add_one_iff {tblL tbl m d : V} (hm : 1 ≤ m) :
    LenGraph tblL tbl (2 * m + 1) d ↔ ∃ d', LenGraph tblL tbl m d' ∧
      d = step2 tblL 3 (lengthEqFact m) d' (succFact ‖m‖) (succCode tbl ‖m‖)
            (vecOf [bnum m, bnum ‖m‖, bnum (‖m‖ + 1)]) (lengthEqFact (2 * m + 1)) := by
  rw [LenGraph.case_iff]
  constructor
  · rintro (⟨h, _⟩ | ⟨h, _⟩ | ⟨m', _, _, h, _⟩ | ⟨m', d', _, h, hd', rfl⟩)
    · exact absurd h (two_mul_add_one_ne_zero m)
    · exact absurd h (two_mul_add_one_ne_one hm)
    · exact absurd h.symm (two_mul_ne_two_mul_add_one m' m)
    · obtain rfl := two_mul_add_one_inj h; exact ⟨d', hd', rfl⟩
  · rintro ⟨d', hd', rfl⟩; exact Or.inr (Or.inr (Or.inr ⟨m, d', hm, rfl, hd', rfl⟩))

lemma lenGraph_exists (tblL tbl z : V) : ∃ d, LenGraph tblL tbl z d := by
  induction z using ISigma1.sigma1_order_induction with
  | hP => definability
  | ind z ih =>
    rcases zero_one_or_two_le z with rfl | rfl | h2
    · exact ⟨_, LenGraph.zero_iff.mpr rfl⟩
    · exact ⟨_, LenGraph.one_iff.mpr rfl⟩
    obtain ⟨hm, hlt, he | ho⟩ := two_le_cases h2
    · obtain ⟨d', hd'⟩ := ih (z / 2) hlt
      rw [he]; exact ⟨_, (LenGraph.two_mul_iff hm).mpr ⟨d', hd', rfl⟩⟩
    · obtain ⟨d', hd'⟩ := ih (z / 2) hlt
      rw [ho]; exact ⟨_, (LenGraph.two_mul_add_one_iff hm).mpr ⟨d', hd', rfl⟩⟩

lemma lenGraph_unique (tblL tbl z : V) : ∀ d₁ d₂, LenGraph tblL tbl z d₁ → LenGraph tblL tbl z d₂ → d₁ = d₂ := by
  induction z using ISigma1.pi1_order_induction with
  | hP => definability
  | ind z ih =>
    intro d₁ d₂ h₁ h₂
    rcases zero_one_or_two_le z with rfl | rfl | h2
    · rw [LenGraph.zero_iff] at h₁ h₂; rw [h₁, h₂]
    · rw [LenGraph.one_iff] at h₁ h₂; rw [h₁, h₂]
    obtain ⟨hm, hlt, he | ho⟩ := two_le_cases h2
    · rw [he] at h₁ h₂
      obtain ⟨e₁, he₁, rfl⟩ := (LenGraph.two_mul_iff hm).mp h₁
      obtain ⟨e₂, he₂, rfl⟩ := (LenGraph.two_mul_iff hm).mp h₂
      rw [ih (z / 2) hlt e₁ e₂ he₁ he₂]
    · rw [ho] at h₁ h₂
      obtain ⟨e₁, he₁, rfl⟩ := (LenGraph.two_mul_add_one_iff hm).mp h₁
      obtain ⟨e₂, he₂, rfl⟩ := (LenGraph.two_mul_add_one_iff hm).mp h₂
      rw [ih (z / 2) hlt e₁ e₂ he₁ he₂]

lemma lenGraph_existsUnique (tblL tbl z : V) : ∃! d, LenGraph tblL tbl z d := by
  obtain ⟨d, hd⟩ := lenGraph_exists tblL tbl z
  exact ExistsUnique.intro d hd (fun d' h' ↦ lenGraph_unique tblL tbl z d' d h' hd)

/-- **N5's prover**: the derivation code of `{bnum ‖k‖ = ‖bnum k‖}`. -/
noncomputable def lengthEqCode (tblL tbl k : V) : V := Classical.choose! (lenGraph_existsUnique tblL tbl k)

lemma lengthEqCode_graph (tblL tbl k : V) : LenGraph tblL tbl k (lengthEqCode tblL tbl k) :=
  Classical.choose!_spec (lenGraph_existsUnique tblL tbl k)

lemma lengthEqCode_eq_of_graph {tblL tbl k d : V} (h : LenGraph tblL tbl k d) : lengthEqCode tblL tbl k = d :=
  lenGraph_unique tblL tbl k _ _ (lengthEqCode_graph tblL tbl k) h

noncomputable def lengthEqCodeDef : 𝚺₁.Semisentence 4 := .mkSigma “y tblL tbl k. !lenGraphDef tblL tbl k y”

/-- The `succCode_defined` pattern: never a blanket `simp` through the fixpoint formula. -/
instance lengthEqCode_defined : 𝚺₁-Function₃ (lengthEqCode : V → V → V → V) via lengthEqCodeDef := .mk fun v ↦ by
  simp only [lengthEqCodeDef]
  rw [HierarchySymbol.Semiformula.val_mkSigma, Semiformula.eval_substs ![#1, #2, #3, #0] lenGraphDef.val,
    lenGraph_defined.iff]
  simp only [Function.comp_apply, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_two,
    Matrix.tail_cons, Matrix.cons_val_three, Semiterm.val_bvar, Fin.succ_zero_eq_one, Fin.succ_one_eq_two]
  constructor
  · intro h; exact (lengthEqCode_eq_of_graph h).symm
  · intro h; rw [h]; exact lengthEqCode_graph _ _ _
instance lengthEqCode_definable : 𝚺₁-Function₃ (lengthEqCode : V → V → V → V) := lengthEqCode_defined.to_definable

end lenGraph


/-! ## 5. Soundness and length of `lengthEqCode`; its `sLemma` packaging

Per node the cap `nodeCap N B N' B' z := nodeCost N' B' (12‖z‖ + 3) + ltCap N B z + (‖z‖ + 1) · nodeCost N B
(12‖z‖ + 3)` (the row use, the `0 < bnum m` sub-derivation, the successor sub-derivation), monotone in
`‖z‖`; `‖z‖ + 1` nodes: `lengthEqBound := (‖z‖ + 1) · nodeCap` — quadratic in `‖z‖` through `ltCode`. -/

section lenSound

/-- The `ltCode tbl 0 m` cap for `1 ≤ m ≤ z`. -/
noncomputable def ltCap (N B z : V) : V := (2 * ‖z‖ + 7) * nodeCost N B (12 * ‖z‖ + 3)
/-- The per-node cap. -/
noncomputable def nodeCap (N B N' B' z : V) : V :=
  nodeCost N' B' (12 * ‖z‖ + 3) + ltCap N B z + (‖z‖ + 1) * nodeCost N B (12 * ‖z‖ + 3)
/-- The length bound of `lengthEqCode`: `‖z‖ + 1` nodes, each `≤ nodeCap`. -/
noncomputable def lengthEqBound (N B N' B' z : V) : V := (‖z‖ + 1) * nodeCap N B N' B' z

lemma dlen_ltCode_zero_le {tbl N B : V} (htbl : NumTableOK tbl N B) {m z : V} (hm : 1 ≤ m) (hmz : m ≤ z) :
    dlen TAct (ltCode tbl 0 m) ≤ ltCap N B z := by
  have h0m : (0 : V) < m := lt_of_lt_of_le _root_.zero_lt_one hm
  have hlz : ‖m‖ ≤ ‖z‖ := length_monotone hmz
  have h1z : 1 ≤ ‖z‖ := by
    have := length_monotone (le_trans hm hmz); rwa [length_one] at this
  have hEm : 12 * ‖m‖ + 3 ≤ 12 * ‖z‖ + 3 := add_le_add (mul_le_mul_of_nonneg_left hlz zero_le) le_rfl
  have hCm : nodeCost N B (12 * ‖m‖ + 3) ≤ nodeCost N B (12 * ‖z‖ + 3) := nodeCost_mono hEm
  have h12 : (6 : V) * 1 + 3 ≤ 12 * ‖z‖ + 3 :=
    add_le_add (by rw [mul_one]; exact le_trans (by norm_num) (le_mul_of_one_le_right zero_le h1z)) le_rfl
  have hsucc : dlen TAct (succCode tbl 0) ≤ nodeCost N B (12 * ‖z‖ + 3) := by
    refine le_trans (dlen_succCode_le htbl 0) ?_
    rw [length_zero, zero_add, length_one, one_mul]
    exact nodeCost_mono h12
  have hle : dlen TAct (leCode tbl 1 m) ≤
      2 * (‖z‖ + 2) * nodeCost N B (12 * ‖z‖ + 3) + nodeCost N B (12 * ‖z‖ + 3) := by
    refine le_trans (dlen_leCode_le htbl hm) ?_
    refine add_le_add ?_ hCm
    refine le_trans (dlen_addCode_le htbl 1 (m - 1)) ?_
    rw [add_tsub_cancel_of_le hm, length_one, one_add_one_eq_two]
    refine mul_le_mul ?_ hCm zero_le zero_le
    exact mul_le_mul_of_nonneg_left (add_le_add hlz le_rfl) zero_le
  have hlt := dlen_ltCode_le htbl h0m
  rw [zero_add] at hlt
  refine le_trans hlt ?_
  unfold ltCap
  calc dlen TAct (succCode tbl 0) + dlen TAct (leCode tbl 1 m) + nodeCost N B (12 * ‖m‖ + 3)
      ≤ nodeCost N B (12 * ‖z‖ + 3) + (2 * (‖z‖ + 2) * nodeCost N B (12 * ‖z‖ + 3) + nodeCost N B (12 * ‖z‖ + 3))
        + nodeCost N B (12 * ‖z‖ + 3) := add_le_add (add_le_add hsucc hle) hCm
    _ = (2 * ‖z‖ + 7) * nodeCost N B (12 * ‖z‖ + 3) := by ring

lemma nodeCap_mono {N B N' B' m z : V} (h : ‖m‖ ≤ ‖z‖) : nodeCap N B N' B' m ≤ nodeCap N B N' B' z := by
  unfold nodeCap ltCap
  have hE : 12 * ‖m‖ + 3 ≤ 12 * ‖z‖ + 3 := add_le_add (mul_le_mul_of_nonneg_left h zero_le) le_rfl
  refine add_le_add (add_le_add (nodeCost_mono hE) ?_) ?_
  · exact mul_le_mul (add_le_add (mul_le_mul_of_nonneg_left h zero_le) le_rfl) (nodeCost_mono hE) zero_le zero_le
  · exact mul_le_mul (add_le_add h le_rfl) (nodeCost_mono hE) zero_le zero_le

/-- The successor sub-derivation at the LENGTH numeral, for `m ≤ z` and `‖m‖ + 1 ≤ z`. -/
lemma dlen_succCode_length_le {tbl N B : V} (htbl : NumTableOK tbl N B) {m z : V} (hmz : m ≤ z) (hlz : ‖m‖ + 1 ≤ z) :
    dlen TAct (succCode tbl ‖m‖) ≤ (‖z‖ + 1) * nodeCost N B (12 * ‖z‖ + 3) := by
  refine le_trans (dlen_succCode_le htbl _) ?_
  refine mul_le_mul (add_le_add (le_trans (length_monotone (length_le m)) (length_monotone hmz)) le_rfl) ?_
    zero_le zero_le
  refine nodeCost_mono ?_
  have := length_monotone hlz
  calc 6 * ‖‖m‖ + 1‖ + 3 ≤ 6 * ‖z‖ + 3 := add_le_add (mul_le_mul_of_nonneg_left this zero_le) le_rfl
    _ ≤ 12 * ‖z‖ + 3 := add_le_add (mul_le_mul_of_nonneg_right (by norm_num) zero_le) le_rfl

lemma succE_le_lenE {m z : V} (hlz : ‖m‖ + 1 ≤ z) : 6 * ‖‖m‖ + 1‖ + 3 ≤ 12 * ‖z‖ + 3 := by
  have := length_monotone hlz
  calc 6 * ‖‖m‖ + 1‖ + 3 ≤ 6 * ‖z‖ + 3 := add_le_add (mul_le_mul_of_nonneg_left this zero_le) le_rfl
    _ ≤ 12 * ‖z‖ + 3 := add_le_add (mul_le_mul_of_nonneg_right (by norm_num) zero_le) le_rfl

lemma lenE_mono {m z : V} (h : m ≤ z) : 12 * ‖m‖ + 3 ≤ 12 * ‖z‖ + 3 :=
  add_le_add (mul_le_mul_of_nonneg_left (length_monotone h) zero_le) le_rfl

/-- **Soundness and length of the length chain**, by Π₁ order induction on `z`. -/
theorem lenGraph_sound {tbl N B tblL N' B' : V} (htbl : NumTableOK tbl N B) (htblL : LenTableOK tblL N' B') (z : V) :
    ∀ d, LenGraph tblL tbl z d →
      DerivationOf TAct d (sing (lengthEqFact z)) ∧ dlen TAct d ≤ lengthEqBound N B N' B' z := by
  induction z using ISigma1.pi1_order_induction with
  | hP => simp only [lengthEqBound, nodeCap, ltCap]; definability
  | ind z ih =>
    intro d hd
    obtain ⟨hr0, hr1, hr2, hr3, hPlen, hPeq, hPlt, hB⟩ := htblL
    have hx0 : IsSemiterm LAct 0 (bnum (0 : V)) := isSemiterm_bnum_LAct 0 _
    rcases zero_one_or_two_le z with rfl | rfl | h2
    · rw [LenGraph.zero_iff] at hd
      subst hd
      have hc : instOuter LAct [bnum 0] row_lengthZero_c = lengthEqFact (0 : V) := by
        rw [(inst_lengthZero hx0).2, lengthEqFact_zero]
      have hes : ∀ e ∈ [bnum (0 : V)], IsSemiterm LAct 0 e ∧ termLen LAct e ≤ 12 * ‖(0 : V)‖ + 3 := by
        simp only [List.mem_singleton, forall_eq]
        exact ⟨hx0, termLen_bnum_le_E' le_rfl le_rfl⟩
      have hpf := step0_proof hr0 [bnum 0] rfl (fun e he ↦ (hes e he).1) (isFormula_lengthEqFact 0) (inst_lengthZero hx0).1 hc
      have hlen := dlen_step0_le hr0 [bnum 0] rfl hes one_le_addE hB (isFormula_lengthEqFact 0) (inst_lengthZero hx0).1 hc
        (by norm_num) (by simp [row_lengthZero_as]) (formulaLen_lengthEqFact_le hPlen le_rfl)
      rw [cast_rLenZero] at hpf hlen
      refine ⟨hpf, ?_⟩
      unfold lengthEqBound nodeCap
      exact le_trans hlen (le_trans (le_trans le_self_add le_self_add) (le_mul_of_one_le_left zero_le le_add_self))
    · rw [LenGraph.one_iff] at hd
      subst hd
      have hc : instOuter LAct [bnum 0] row_lengthOne_c = lengthEqFact (1 : V) := by
        rw [(inst_lengthOne hx0).2, lengthEqFact_one]
      have hes : ∀ e ∈ [bnum (0 : V)], IsSemiterm LAct 0 e ∧ termLen LAct e ≤ 12 * ‖(1 : V)‖ + 3 := by
        simp only [List.mem_singleton, forall_eq]
        exact ⟨hx0, termLen_bnum_le_E' zero_le le_rfl⟩
      have hpf := step0_proof hr1 [bnum 0] rfl (fun e he ↦ (hes e he).1) (isFormula_lengthEqFact 1) (inst_lengthOne hx0).1 hc
      have hlen := dlen_step0_le hr1 [bnum 0] rfl hes one_le_addE hB (isFormula_lengthEqFact 1) (inst_lengthOne hx0).1 hc
        (by norm_num) (by simp [row_lengthOne_as]) (formulaLen_lengthEqFact_le hPlen le_rfl)
      rw [cast_rLenOne] at hpf hlen
      refine ⟨hpf, ?_⟩
      unfold lengthEqBound nodeCap
      exact le_trans hlen (le_trans (le_trans le_self_add le_self_add) (le_mul_of_one_le_left zero_le le_add_self))
    obtain ⟨hm, hlt, he | ho⟩ := two_le_cases h2
    · rw [he] at hd ⊢
      obtain ⟨d', hd', rfl⟩ := (LenGraph.two_mul_iff hm).mp hd
      obtain ⟨hpf', hlen'⟩ := ih (z / 2) hlt d' hd'
      set m := z / 2 with hm_def
      have hpos : (0 : V) < m := lt_of_lt_of_le _root_.zero_lt_one hm
      have hx : IsSemiterm LAct 0 (bnum m) := isSemiterm_bnum_LAct 0 _
      have hl : IsSemiterm LAct 0 (bnum ‖m‖) := isSemiterm_bnum_LAct 0 _
      have hl' : IsSemiterm LAct 0 (bnum (‖m‖ + 1)) := isSemiterm_bnum_LAct 0 _
      have hm2 : m ≤ 2 * m := le_of_lt (Bnum.lt_two_mul hm)
      have hlz : ‖m‖ + 1 ≤ 2 * m := by
        rw [two_mul]; exact le_trans (add_le_add (length_le m) le_rfl) (add_le_add le_rfl hm)
      have hlm : ‖m‖ ≤ 2 * m := le_trans le_self_add hlz
      have hes : ∀ e ∈ [bnum m, bnum ‖m‖, bnum (‖m‖ + 1)], IsSemiterm LAct 0 e ∧ termLen LAct e ≤ 12 * ‖2 * m‖ + 3 := by
        intro e he
        simp only [List.mem_cons, List.mem_singleton, List.not_mem_nil, or_false] at he
        rcases he with rfl | rfl | rfl
        · exact ⟨hx, termLen_bnum_le_E' hm2 le_rfl⟩
        · exact ⟨hl, termLen_bnum_le_E' hlm le_rfl⟩
        · exact ⟨hl', termLen_bnum_le_E' hlz le_rfl⟩
      set ps : List (V × V) := [(lengthEqFact m, d'), (ltFact (bnum 0) (bnum m), ltCode tbl 0 m),
        (succFact ‖m‖, succCode tbl ‖m‖)] with hps_def
      have hps : ∀ p ∈ ps, IsFormula LAct p.1 ∧ DerivationOf TAct p.2 (sing p.1) := by
        intro p hp
        simp only [hps_def, List.mem_cons, List.mem_singleton, List.not_mem_nil, or_false] at hp
        rcases hp with rfl | rfl | rfl
        · exact ⟨isFormula_lengthEqFact m, hpf'⟩
        · exact ⟨isFormula_ltFact_bnum 0 m, ltCode_proof htbl hpos⟩
        · exact ⟨isFormula_succFact _, succCode_proof htbl _⟩
      have hmap : row_lenTwoMulS_as.map (instOuter LAct [bnum m, bnum ‖m‖, bnum (‖m‖ + 1)]) = ps.map Prod.fst := by
        rw [(inst_lenTwoMulS hx hl hl').1]
        simp only [hps_def, List.map_cons, List.map_nil, lengthEqFact, succFact, eqFactB_eq_eqFact, bnum_zero]
      have hc : instOuter LAct [bnum m, bnum ‖m‖, bnum (‖m‖ + 1)] row_lenTwoMulS_c = lengthEqFact (2 * m) := by
        rw [(inst_lenTwoMulS hx hl hl').2, lengthEqFact_two_mul hm]
      have hpsP : ∀ p ∈ ps, formulaLen LAct p.1 ≤ B' * (12 * ‖2 * m‖ + 3) := by
        intro p hp
        simp only [hps_def, List.mem_cons, List.mem_singleton, List.not_mem_nil, or_false] at hp
        rcases hp with rfl | rfl | rfl
        · exact formulaLen_lengthEqFact_le hPlen (lenE_mono hm2)
        · exact formulaLen_ltFact_bnum_le hPlt zero_le hm2 le_rfl
        · exact formulaLen_succFact_le hPeq (succE_le_lenE hlz)
      rw [← stepL_three]
      have hpf := stepL_proof hr2 ps [bnum m, bnum ‖m‖, bnum (‖m‖ + 1)] rfl (fun e he ↦ (hes e he).1)
        (isFormula_lengthEqFact _) hps hmap hc
      have hlen := dlen_stepL_le hr2 ps [bnum m, bnum ‖m‖, bnum (‖m‖ + 1)] rfl hes one_le_addE hB
        (isFormula_lengthEqFact _) hps hmap hc (by norm_num) (by simp [row_lenTwoMulS_as])
        (formulaLen_lengthEqFact_le hPlen le_rfl) hpsP
      rw [cast_rLenTwoMul] at hpf hlen
      refine ⟨hpf, ?_⟩
      have h1 : dlen TAct d' ≤ (‖m‖ + 1) * nodeCap N B N' B' (2 * m) := by
        unfold lengthEqBound at hlen'
        exact le_trans hlen' (mul_le_mul_of_nonneg_left (nodeCap_mono (length_monotone hm2)) zero_le)
      have h2 : dlen TAct (ltCode tbl 0 m) ≤ ltCap N B (2 * m) := dlen_ltCode_zero_le htbl hm hm2
      have h3 : dlen TAct (succCode tbl ‖m‖) ≤ (‖2 * m‖ + 1) * nodeCost N B (12 * ‖2 * m‖ + 3) :=
        dlen_succCode_length_le htbl hm2 hlz
      unfold lengthEqBound
      calc dlen TAct (stepL tblL 2 ps (vecOf [bnum m, bnum ‖m‖, bnum (‖m‖ + 1)]) (lengthEqFact (2 * m)))
          ≤ factsDlen ps + nodeCost N' B' (12 * ‖2 * m‖ + 3) := hlen
        _ = dlen TAct d' + dlen TAct (ltCode tbl 0 m) + dlen TAct (succCode tbl ‖m‖) + nodeCost N' B' (12 * ‖2 * m‖ + 3) := by
            simp only [hps_def, factsDlen_cons, factsDlen_nil]; ring
        _ ≤ (‖m‖ + 1) * nodeCap N B N' B' (2 * m) + ltCap N B (2 * m) + (‖2 * m‖ + 1) * nodeCost N B (12 * ‖2 * m‖ + 3)
            + nodeCost N' B' (12 * ‖2 * m‖ + 3) := add_le_add (add_le_add (add_le_add h1 h2) h3) le_rfl
        _ = (‖2 * m‖ + 1) * nodeCap N B N' B' (2 * m) := by
            unfold nodeCap; rw [length_two_mul_of_pos hpos]; ring
    · rw [ho] at hd ⊢
      obtain ⟨d', hd', rfl⟩ := (LenGraph.two_mul_add_one_iff hm).mp hd
      obtain ⟨hpf', hlen'⟩ := ih (z / 2) hlt d' hd'
      set m := z / 2 with hm_def
      have hx : IsSemiterm LAct 0 (bnum m) := isSemiterm_bnum_LAct 0 _
      have hl : IsSemiterm LAct 0 (bnum ‖m‖) := isSemiterm_bnum_LAct 0 _
      have hl' : IsSemiterm LAct 0 (bnum (‖m‖ + 1)) := isSemiterm_bnum_LAct 0 _
      have hm2 : m ≤ 2 * m + 1 := le_of_lt (Bnum.lt_two_mul_add_one hm)
      have hlz : ‖m‖ + 1 ≤ 2 * m + 1 := by
        refine le_trans ?_ (le_self_add : 2 * m ≤ 2 * m + 1)
        rw [two_mul]; exact le_trans (add_le_add (length_le m) le_rfl) (add_le_add le_rfl hm)
      have hlm : ‖m‖ ≤ 2 * m + 1 := le_trans le_self_add hlz
      have hes : ∀ e ∈ [bnum m, bnum ‖m‖, bnum (‖m‖ + 1)], IsSemiterm LAct 0 e ∧ termLen LAct e ≤ 12 * ‖2 * m + 1‖ + 3 := by
        intro e he
        simp only [List.mem_cons, List.mem_singleton, List.not_mem_nil, or_false] at he
        rcases he with rfl | rfl | rfl
        · exact ⟨hx, termLen_bnum_le_E' hm2 le_rfl⟩
        · exact ⟨hl, termLen_bnum_le_E' hlm le_rfl⟩
        · exact ⟨hl', termLen_bnum_le_E' hlz le_rfl⟩
      set ps : List (V × V) := [(lengthEqFact m, d'), (succFact ‖m‖, succCode tbl ‖m‖)] with hps_def
      have hps : ∀ p ∈ ps, IsFormula LAct p.1 ∧ DerivationOf TAct p.2 (sing p.1) := by
        intro p hp
        simp only [hps_def, List.mem_cons, List.mem_singleton, List.not_mem_nil, or_false] at hp
        rcases hp with rfl | rfl
        · exact ⟨isFormula_lengthEqFact m, hpf'⟩
        · exact ⟨isFormula_succFact _, succCode_proof htbl _⟩
      have hmap : row_lenTwoMulOneS_as.map (instOuter LAct [bnum m, bnum ‖m‖, bnum (‖m‖ + 1)]) = ps.map Prod.fst := by
        rw [(inst_lenTwoMulOneS hx hl hl').1]
        simp only [hps_def, List.map_cons, List.map_nil, lengthEqFact, succFact, eqFactB_eq_eqFact]
      have hc : instOuter LAct [bnum m, bnum ‖m‖, bnum (‖m‖ + 1)] row_lenTwoMulOneS_c = lengthEqFact (2 * m + 1) := by
        rw [(inst_lenTwoMulOneS hx hl hl').2, lengthEqFact_two_mul_add_one hm]
      have hpsP : ∀ p ∈ ps, formulaLen LAct p.1 ≤ B' * (12 * ‖2 * m + 1‖ + 3) := by
        intro p hp
        simp only [hps_def, List.mem_cons, List.mem_singleton, List.not_mem_nil, or_false] at hp
        rcases hp with rfl | rfl
        · exact formulaLen_lengthEqFact_le hPlen (lenE_mono hm2)
        · exact formulaLen_succFact_le hPeq (succE_le_lenE hlz)
      rw [← stepL_two]
      have hpf := stepL_proof hr3 ps [bnum m, bnum ‖m‖, bnum (‖m‖ + 1)] rfl (fun e he ↦ (hes e he).1)
        (isFormula_lengthEqFact _) hps hmap hc
      have hlen := dlen_stepL_le hr3 ps [bnum m, bnum ‖m‖, bnum (‖m‖ + 1)] rfl hes one_le_addE hB
        (isFormula_lengthEqFact _) hps hmap hc (by norm_num) (by simp [row_lenTwoMulOneS_as])
        (formulaLen_lengthEqFact_le hPlen le_rfl) hpsP
      rw [cast_rLenTwoMulOne] at hpf hlen
      refine ⟨hpf, ?_⟩
      have h1 : dlen TAct d' ≤ (‖m‖ + 1) * nodeCap N B N' B' (2 * m + 1) := by
        unfold lengthEqBound at hlen'
        exact le_trans hlen' (mul_le_mul_of_nonneg_left (nodeCap_mono (length_monotone hm2)) zero_le)
      have h3 : dlen TAct (succCode tbl ‖m‖) ≤ (‖2 * m + 1‖ + 1) * nodeCost N B (12 * ‖2 * m + 1‖ + 3) :=
        dlen_succCode_length_le htbl hm2 hlz
      unfold lengthEqBound
      calc dlen TAct (stepL tblL 3 ps (vecOf [bnum m, bnum ‖m‖, bnum (‖m‖ + 1)]) (lengthEqFact (2 * m + 1)))
          ≤ factsDlen ps + nodeCost N' B' (12 * ‖2 * m + 1‖ + 3) := hlen
        _ = dlen TAct d' + dlen TAct (succCode tbl ‖m‖) + nodeCost N' B' (12 * ‖2 * m + 1‖ + 3) := by
            simp only [hps_def, factsDlen_cons, factsDlen_nil]; ring
        _ ≤ (‖m‖ + 1) * nodeCap N B N' B' (2 * m + 1) + (‖2 * m + 1‖ + 1) * nodeCost N B (12 * ‖2 * m + 1‖ + 3)
            + nodeCost N' B' (12 * ‖2 * m + 1‖ + 3) := add_le_add (add_le_add h1 h3) le_rfl
        _ ≤ (‖m‖ + 1) * nodeCap N B N' B' (2 * m + 1) + ltCap N B (2 * m + 1)
            + (‖2 * m + 1‖ + 1) * nodeCost N B (12 * ‖2 * m + 1‖ + 3) + nodeCost N' B' (12 * ‖2 * m + 1‖ + 3) := by
            refine add_le_add (add_le_add ?_ le_rfl) le_rfl
            exact le_self_add
        _ = (‖2 * m + 1‖ + 1) * nodeCap N B N' B' (2 * m + 1) := by
            unfold nodeCap; rw [length_two_mul_add_one]; ring

/-- **`lengthEqCode` is a derivation of `{bnum ‖k‖ = ‖bnum k‖}`**, in every model, over any sound tables. -/
theorem lengthEqCode_proof {tbl N B tblL N' B' : V} (htbl : NumTableOK tbl N B) (htblL : LenTableOK tblL N' B') (k : V) :
    DerivationOf TAct (lengthEqCode tblL tbl k) (sing (lengthEqFact k)) :=
  (lenGraph_sound htbl htblL k _ (lengthEqCode_graph tblL tbl k)).1

/-- **`dlen (lengthEqCode tblL tbl k) ≤ (‖k‖ + 1) · nodeCap`** — quadratic in the bit length. -/
theorem dlen_lengthEqCode_le {tbl N B tblL N' B' : V} (htbl : NumTableOK tbl N B) (htblL : LenTableOK tblL N' B') (k : V) :
    dlen TAct (lengthEqCode tblL tbl k) ≤ lengthEqBound N B N' B' k :=
  (lenGraph_sound htbl htblL k _ (lengthEqCode_graph tblL tbl k)).2

/-- The `sLemma` step of N5 is applicable … -/
theorem lemmaOK_lengthEq {tbl N B tblL N' B' : V} (htbl : NumTableOK tbl N B) (htblL : LenTableOK tblL N' B') (k : V) :
    LemmaOK (sLemma (lengthEqFact k) (lengthEqCode tblL tbl k)) :=
  lemmaOK_of (isFormula_lengthEqFact k) (lengthEqCode_proof htbl htblL k)

/-- … and its cost: `≤ lengthEqBound + 2|Γ| + 2|lengthEqFact k| + 2`. -/
theorem stepCost_lemma_lengthEq {tbl N B tblL N' B' N'' E Γ : V} (htbl : NumTableOK tbl N B) (htblL : LenTableOK tblL N' B') (k : V) :
    stepCost N'' E Γ (sLemma (lengthEqFact k) (lengthEqCode tblL tbl k)) ≤
      lengthEqBound N B N' B' k + 2 * setLen LAct Γ + 2 * formulaLen LAct (lengthEqFact k) + 2 := by
  rw [stepCost_sLemma]
  exact add_le_add (add_le_add (add_le_add (dlen_lengthEqCode_le htbl htblL k) le_rfl) le_rfl) le_rfl

end lenSound

end ArithS
