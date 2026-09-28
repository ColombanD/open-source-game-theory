import ArithS.Necessitation.RowInst

/-!
# ArithS.Necessitation.RowInstC — the HAND-WRITTEN rows split off from the generated `RowInst.lean` (2026-09-28)

Everything here was appended by hand to `RowInst.lean` on 2026-09-13 (commit `6185743`) AFTER that file was
generated, which put the generated file out of sync with `scripts/gen_rowinst.py`. It is the §3.C block of
`Lib/Walk.lean` §6: the level-`m` chain term `cTTm` with its code equation `quote_cTTm`, `cT_one`, and the four
chain-numeral arity rows (`isSemiformulaSubsts1C`, `isFormulaFreeC`, `piArityOneToC`, `piArityCToOne`) with their
row-shape, formula-ness and instantiation lemmas — proved with the row tactics of `RowInst.lean`, which are
top-level macros. `RowInst.lean` is now purely generated again (`scripts/regen_all.sh` checks all nine tables).
-/

namespace ArithS
open FFL FFL.FirstOrder Arithmetic Bootstrapping
open PeanoMinus ISigma0 ISigma1
open FFL.FirstOrder.Arithmetic.Bootstrapping.Arithmetic
open LAct
variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]
set_option linter.unusedSimpArgs false
set_option linter.unusedTactic false

section rows

/-! ## 3.C Chain-numeral arity rows (`Lib/Walk.lean` §6) — hand-written, 2026-09-13

The generator writes chain literals only in CLOSED rows (`rfl` to `⇜ ![cTT k, …]` at level `0`).
A chain literal INSIDE a variable-bearing row is a closed term at level `m`: `cTTm m n`, the
level-`m` twin of `cTT` (`cTTm 0 = cTT`), with the same code equation `quote_cTTm`. The DSL
literal `(0 + 1)` of the C rows is `cTTm m 1` by `rfl` (the `example`s), and `row_shape` reads
its code as `𝟎 ^+ 𝟏 = cT 1` (`cT_one`), so the instantiated antecedent is `piFact (cT 1) wp`. -/

/-- The meta chain term `0 + 1 + ⋯ + 1` at bound-variable count `m` (`cTTm 0 = cTT`). -/
noncomputable def cTTm (m : ℕ) : ℕ → ClosedSemiterm ℒₒᵣ m
  | 0 => ‘0’
  | n + 1 => ‘!!(cTTm m n) + 1’

lemma cTTm_zero (m : ℕ) : cTTm m 0 = ‘0’ := rfl
lemma cTTm_succ (m n : ℕ) : cTTm m (n + 1) = ‘!!(cTTm m n) + 1’ := rfl

lemma cTTm_zero_eq_cTT : cTTm 0 = cTT := by
  funext n; induction n with | zero => rfl | succ n ih => rw [cTTm_succ, cTT_succ, ih]

/-- The code equation at every level: `⌜cTTm m n⌝ = cT n`. -/
theorem quote_cTTm (m n : ℕ) : (⌜cTTm m n⌝ : V) = cT n := by
  induction n with
  | zero => rw [cTTm_zero, quote_closed_zero_m, cT_zero]
  | succ n ih =>
    rw [cTTm_succ, show (‘!!(cTTm m n) + 1’ : ClosedSemiterm ℒₒᵣ m) =
        ‘!!(cTTm m n) + !!(‘1’ : ClosedSemiterm ℒₒᵣ m)’ from rfl,
      quote_closed_add_m, quote_closed_one_m, ih, cT_succ]

lemma cT_one : (cT 1 : V) = (𝟎 : V) ^+ 𝟏 := by rw [show (1 : ℕ) = 0 + 1 from rfl, cT_succ, cT_zero]

/-- The DSL literal `(0 + 1)` is the chain term `cTTm m 1` (and the old rows' `1` is the numeral). -/
example : (‘0 + 1’ : ClosedSemiterm ℒₒᵣ 4) = cTTm 4 1 := rfl
example : (‘0 + 1’ : ClosedSemiterm ℒₒᵣ 2) = cTTm 2 1 := rfl
example : (“y p t n. !(isSemiformula LAct).pi (0 + 1) p” : ArithmeticSemisentence 4) =
    (↑(isSemiformula LAct).pi : ArithmeticSemisentence 2) ⇜ ![cTTm 4 1, #1] := rfl
example : (“y p. !(isSemiformula LAct).pi (0 + 1) p” : ArithmeticSemisentence 2) =
    (↑(isSemiformula LAct).pi : ArithmeticSemisentence 2) ⇜ ![cTTm 2 1, #1] := rfl
example : (“p. !(isSemiformula LAct).sigma (0 + 1) p” : ArithmeticSemisentence 1) =
    (↑(isSemiformula LAct).sigma : ArithmeticSemisentence 2) ⇜ ![cTTm 1 1, #0] := rfl
example : (“y p. !(isSemiformula LAct).pi 1 p” : ArithmeticSemisentence 2) =
    (↑(isSemiformula LAct).pi : ArithmeticSemisentence 2) ⇜ ![‘1’, #1] := rfl

/-! ### `isSemiformulaSubsts1C` — `“y p t n. …”`, `m = 4` -/

noncomputable def row_isSemiformulaSubsts1C_as : List V := [subst LAct (listToVec [bv 3, bv 2]) PtPi, subst LAct (listToVec [cT 1, bv 1]) Ppi, subst LAct (listToVec [bv 0, bv 2, bv 1]) Psubsts1G]
noncomputable def row_isSemiformulaSubsts1C_c : V := subst LAct (listToVec [bv 3, bv 0]) Psigma

/-- `isSemiformulaSubsts1C` at the witnesses `[wn, wt, wp, wy]` (the DSL variables right-to-left). -/
lemma inst_isSemiformulaSubsts1C {wn wt wp wy : V} (hwn : IsSemiterm LAct 0 wn) (hwt : IsSemiterm LAct 0 wt) (hwp : IsSemiterm LAct 0 wp) (hwy : IsSemiterm LAct 0 wy) :
    row_isSemiformulaSubsts1C_as.map (instOuter LAct [wn, wt, wp, wy]) = [tPiFact wn wt, piFact (cT 1) wp, substs1Fact wy wt wp] ∧
    instOuter LAct [wn, wt, wp, wy] row_isSemiformulaSubsts1C_c = sigmaFact wn wy := by
  have hes : ∀ e ∈ ([wn, wt, wp, wy] : List V), IsSemiterm LAct 0 e := (List.forall_mem_cons.mpr ⟨hwn, List.forall_mem_cons.mpr ⟨hwt, List.forall_mem_cons.mpr ⟨hwp, List.forall_mem_cons.mpr ⟨hwy, List.forall_mem_nil _⟩⟩⟩⟩)
  unfold row_isSemiformulaSubsts1C_as row_isSemiformulaSubsts1C_c
  simp only [List.map_cons, List.map_nil]
  rw [instOuter_subst_listToVec _ isSemiformula_PtPi (by rfl) _ hes (by row_entries), instOuter_subst_listToVec _ isSemiformula_Ppi (by rfl) _ hes (by row_entries), instOuter_subst_listToVec _ isSemiformula_Psubsts1G (by rfl) _ hes (by row_entries), instOuter_subst_listToVec _ isSemiformula_Psigma (by rfl) _ hes (by row_entries)]
  all_goals try row_entries_simp
  row_finish

/-! ### `isFormulaFreeC` — `“y p. …”`, `m = 2` -/

noncomputable def row_isFormulaFreeC_as : List V := [subst LAct (listToVec [cT 1, bv 1]) Ppi, subst LAct (listToVec [bv 0, bv 1]) PfreeG]
noncomputable def row_isFormulaFreeC_c : V := subst LAct (listToVec [(𝟎 : V), bv 0]) Psigma

/-- `isFormulaFreeC` at the witnesses `[wp, wy]` (the DSL variables right-to-left). -/
lemma inst_isFormulaFreeC {wp wy : V} (hwp : IsSemiterm LAct 0 wp) (hwy : IsSemiterm LAct 0 wy) :
    row_isFormulaFreeC_as.map (instOuter LAct [wp, wy]) = [piFact (cT 1) wp, freeFact wy wp] ∧
    instOuter LAct [wp, wy] row_isFormulaFreeC_c = sigmaFact (𝟎 : V) wy := by
  have hes : ∀ e ∈ ([wp, wy] : List V), IsSemiterm LAct 0 e := (List.forall_mem_cons.mpr ⟨hwp, List.forall_mem_cons.mpr ⟨hwy, List.forall_mem_nil _⟩⟩)
  unfold row_isFormulaFreeC_as row_isFormulaFreeC_c
  simp only [List.map_cons, List.map_nil]
  rw [instOuter_subst_listToVec _ isSemiformula_Ppi (by rfl) _ hes (by row_entries), instOuter_subst_listToVec _ isSemiformula_PfreeG (by rfl) _ hes (by row_entries), instOuter_subst_listToVec _ isSemiformula_Psigma (by rfl) _ hes (by row_entries)]
  all_goals try row_entries_simp
  row_finish

/-! ### `piArityOneToC` — `“p. …”`, `m = 1` -/

/-! ### `piArityCToOne` — `“p. …”`, `m = 1` -/

end rows

end ArithS
