import ArithS.Necessitation.Chain
import ArithS.Necessitation.Lib.Frag

/-!
# ArithS.Necessitation.RowInstB — the fragment rows, read off the DSL and instantiated (GENERATED)

`RowInst.lean`'s three deliverables (the row-shape lemma `quote_row_x`, formula-ness of the pieces,
the instantiation lemma `inst_x` at arbitrary closed witnesses — the DSL variable list read
RIGHT-TO-LEFT) for every row of `Lib/Frag.lean` (`DESIGN_fragments.md` §8.1), plus the predicate
codes and canonical fact codes those rows need beyond `RowInst.lean`/`Chain.lean`: `PeqB`/`eqFactB`
(NumSteps.lean's `Peq`/`eqFact` are the SAME code — `PeqB = Peq` by `rfl` after `unfold eqS`; the names
differ only so that both modules build side by side; unify when both have landed),
`Pmem`/`memFact`, `Pinsert`/`insFact`, `Psubset`/`subsetFact`, `PfsetPi`/`fsetPiFact`,
`PsetShiftG`/`setShiftFact`, `PsetLen`/`sequentLenFact`, `PflenG`/`lenFact`, the term-level graphs,
`Pnth`/`nthFact`, the `axm`(ii) graphs, the node graphs `PaxL`/`axLFact` … `Paxm`/`axmFact`, and
the top's `PdlenDef`/`Pproof`/`PinstB`/`Pg` — each with `IsFormula`-ness, the shift law, the
multiplicative length bound and the occurrence bound. `Chain.lean`'s `Pderiv`/`PfstIdx`/`Pdlen`/
`Ple` (`derFact`/`fstIdxFact`/`proofLenFact`/`leFact`) get the lemmas `Chain` does not state.

**Generated** by `arith/scripts/gen_frag.py` (the row table is shared with `Lib/Frag.lean`); the
header below (§1) is hand-written (`scripts/RowInstB.lean.head`). New over `RowInst.lean`'s §1:
the entries `a + b`/`a * b`/`2` (`quote_closed_mul_mB`, `quote_closed_two_m`, `termSubst_qqMulB`,
`isSemiterm_qqAdd/Mul_LAct`) and the three tactics `row_entriesB`/`row_entries_simpB`/`row_shapeB`
extended to them.
-/

namespace ArithS

open FFL FFL.FirstOrder Arithmetic Bootstrapping
open PeanoMinus ISigma0 ISigma1
open FFL.FirstOrder.Arithmetic.Bootstrapping.Arithmetic
open LAct

variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

set_option linter.unusedSimpArgs false
set_option linter.unusedTactic false

/-! ## 1. Infrastructure: `*`, `2`, and the extended tactics -/

lemma quote_closed_mul_mB {m : ℕ} (t u : ClosedSemiterm ℒₒᵣ m) :
    (⌜(‘!!t * !!u’ : ClosedSemiterm ℒₒᵣ m)⌝ : V) = (⌜t⌝ : V) ^* (⌜u⌝ : V) := by
  rw [Semiterm.empty_quote_eq, Semiterm.empty_typed_quote_mul]; rfl

/-- The DSL literal `2` is the code `𝟏 ^+ 𝟏` (`numeral 2 = numeral 1 ^+ 𝟏`). -/
lemma quote_closed_two_m {m : ℕ} : (⌜(‘2’ : ClosedSemiterm ℒₒᵣ m)⌝ : V) = (𝟏 : V) ^+ (𝟏 : V) := by
  rw [Semiterm.empty_quote_eq, Semiterm.empty_typed_quote_numeral_eq_numeral]
  have h2 : ((2 : ℕ) : V) = 0 + 1 + 1 := by norm_num
  first
  | (rw [h2, numeral_add_two, zero_add, numeral_one])
  | (simp; rw [show (2 : V) = 0 + 1 + 1 by norm_num, numeral_add_two, zero_add, numeral_one])
  | (simp [h2, numeral_add_two, numeral_one])

lemma isUTerm_bv (i : ℕ) : IsUTerm LAct (bv i : V) := (isSemiterm_bv (n := i + 1) (by omega)).isUTerm
lemma isUTerm_qqOne_LAct : IsUTerm LAct (𝟏 : V) := (isSemiterm_qqOne_LAct 0).isUTerm
lemma isUTerm_qqZero_LAct : IsUTerm LAct (𝟎 : V) := (isSemiterm_qqZero_LAct 0).isUTerm
lemma isUTerm_cT (n : ℕ) : IsUTerm LAct (cT n : V) := (cT_semiterm_LAct 0 n).isUTerm
lemma isSemiterm_qqAdd_LAct {n x y : V} (hx : IsSemiterm LAct n x) (hy : IsSemiterm LAct n y) :
    IsSemiterm LAct n (x ^+ y) := by
  unfold qqAdd; exact IsSemiterm.func.mpr ⟨isFunc_LAct_addIndex, by simp [hx, hy]⟩
lemma isSemiterm_qqMul_LAct {n x y : V} (hx : IsSemiterm LAct n x) (hy : IsSemiterm LAct n y) :
    IsSemiterm LAct n (x ^* y) := by
  unfold qqMul; exact IsSemiterm.func.mpr ⟨isFunc_LAct_mul, by simp [hx, hy]⟩
lemma isUTerm_qqAdd_iff {x y : V} : IsUTerm LAct (x ^+ y) ↔ IsUTerm LAct x ∧ IsUTerm LAct y := by
  unfold qqAdd; simp [IsUTerm.func_iff, isFunc_LAct_addIndex]
lemma isUTerm_qqMul_iff {x y : V} : IsUTerm LAct (x ^* y) ↔ IsUTerm LAct x ∧ IsUTerm LAct y := by
  unfold qqMul; simp [IsUTerm.func_iff, isFunc_LAct_mul]
lemma termSubst_qqMulB {w x y : V} (hx : IsUTerm LAct x) (hy : IsUTerm LAct y) :
    termSubst LAct w (x ^* y) = termSubst LAct w x ^* termSubst LAct w y := by
  unfold qqMul
  rw [termSubst_func isFunc_LAct_mul (by simp [hx, hy]), termSubstVec_cons₂ hx hy]

/-- Level-`n` term-ness of every entry of a row piece, now with `+`/`*` entries. -/
macro "row_entriesB" : tactic => `(tactic| (
  repeat' first
    | refine List.forall_mem_cons.mpr ⟨?_, ?_⟩
    | refine isSemiterm_qqAdd_LAct ?_ ?_
    | refine isSemiterm_qqMul_LAct ?_ ?_
  all_goals first
    | exact List.forall_mem_nil _
    | exact isSemiterm_bv (by norm_num)
    | exact isSemiterm_qqZero_LAct _
    | exact isSemiterm_qqOne_LAct _
    | exact cT_semiterm_LAct _ _
    | exact isSemiterm_of_le (by assumption) zero_le
    | exact isSemiterm_of_le (isSemiterm_iterate_termShift (by assumption) _) zero_le
    | simp))

/-- Evaluate the entrywise substitution of an instantiated piece, now with `+`/`*` entries. -/
macro "row_entries_simpB" : tactic => `(tactic| simp (maxDischargeDepth := 8) only [List.map_cons, List.map_nil,
  termSubst_qqAdd', termSubst_qqMulB, isUTerm_bv, isUTerm_qqOne_LAct, isUTerm_qqZero_LAct, isUTerm_cT,
  isUTerm_qqAdd_iff, isUTerm_qqMul_iff, and_self, and_true, true_and, termSubst_bv,
  termSubst_bv_add_one, termSubst_qqZero', termSubst_qqOne', termSubst_cT, bvarList_zero, bvarList_one,
  bvarList_two, bvarList_three, bvarList_four, bvarList_five, List.reverse_cons, List.reverse_nil,
  List.nil_append, List.append_nil, List.cons_append, List.singleton_append, List.getD_cons_zero,
  List.getD_cons_succ])

/-- Read a row body off the DSL, now with `*` and `2`. -/
macro "row_shapeB" : tactic => `(tactic| (
  simp only [Semiformula.Operator.operator, quote_lMap_emb_imp, quote_lMap_emb_ex, quote_lMap_emb_and,
    quote_lMap_emb_subst', impChain_cons, impChain_nil, matrixToVec_fin0, matrixToVec_fin1, matrixToVec_fin2,
    matrixToVec_fin3, matrixToVec_fin4, matrixToVec_fin5, matrixToVec_fin6, matrixToVec_fin7,
    Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.cons_val_three, Matrix.cons_val_four,
    Matrix.head_cons, Matrix.tail_cons,
    quote_closed_add_m, quote_closed_mul_mB, quote_closed_two_m, quote_closed_one_m, quote_closed_zero_m,
    quote_closed_bvar_m, quote_cTT, cT_succ, cT_zero]
  all_goals rfl))

/-! ## 2. The predicate codes and the canonical fact codes not in `RowInst.lean`/`Chain.lean` -/

section facts

/-- The code of `eq` (arity 2). -/
noncomputable def PeqB : V := ⌜Semiformula.lMap emb (Rewriting.emb (Semiformula.Operator.Eq.eq : Semiformula.Operator ℒₒᵣ 2).sentence : ArithmeticSemisentence 2)⌝
lemma isSemiformula_PeqB : IsSemiformula LAct ((2 : ℕ) : V) PeqB := Sentence.quote_isSemiformula _
lemma shift_PeqB : shift LAct (PeqB : V) = PeqB := shift_quote_sentence _

/-- The code of `formulaLenMetaG` (arity 2). -/
noncomputable def PflenG : V := ⌜Semiformula.lMap emb (↑(formulaLenGraph LAct) : ArithmeticSemisentence 2)⌝
lemma isSemiformula_PflenG : IsSemiformula LAct ((2 : ℕ) : V) PflenG := Sentence.quote_isSemiformula _
lemma shift_PflenG : shift LAct (PflenG : V) = PflenG := shift_quote_sentence _

/-- The code of `termLenMetaG` (arity 2). -/
noncomputable def PtlenG : V := ⌜Semiformula.lMap emb (↑(termLenGraph LAct) : ArithmeticSemisentence 2)⌝
lemma isSemiformula_PtlenG : IsSemiformula LAct ((2 : ℕ) : V) PtlenG := Sentence.quote_isSemiformula _
lemma shift_PtlenG : shift LAct (PtlenG : V) = PtlenG := shift_quote_sentence _

/-- The code of `mem` (arity 2). -/
noncomputable def Pmem : V := ⌜Semiformula.lMap emb (Rewriting.emb (Semiformula.Operator.Mem.mem : Semiformula.Operator ℒₒᵣ 2).sentence : ArithmeticSemisentence 2)⌝
lemma isSemiformula_Pmem : IsSemiformula LAct ((2 : ℕ) : V) Pmem := Sentence.quote_isSemiformula _
lemma shift_Pmem : shift LAct (Pmem : V) = Pmem := shift_quote_sentence _

lemma shift_PfstIdx : shift LAct (PfstIdx : V) = PfstIdx := shift_quote_sentence _

/-- The code of `subset` (arity 2). -/
noncomputable def Psubset : V := ⌜Semiformula.lMap emb (↑bitSubsetDef : ArithmeticSemisentence 2)⌝
lemma isSemiformula_Psubset : IsSemiformula LAct ((2 : ℕ) : V) Psubset := Sentence.quote_isSemiformula _
lemma shift_Psubset : shift LAct (Psubset : V) = Psubset := shift_quote_sentence _

/-- The code of `setShiftG` (arity 2). -/
noncomputable def PsetShiftG : V := ⌜Semiformula.lMap emb (↑(setShiftGraph LAct) : ArithmeticSemisentence 2)⌝
lemma isSemiformula_PsetShiftG : IsSemiformula LAct ((2 : ℕ) : V) PsetShiftG := Sentence.quote_isSemiformula _
lemma shift_PsetShiftG : shift LAct (PsetShiftG : V) = PsetShiftG := shift_quote_sentence _

/-- The code of `insert` (arity 3). -/
noncomputable def Pinsert : V := ⌜Semiformula.lMap emb (↑insertDef : ArithmeticSemisentence 3)⌝
lemma isSemiformula_Pinsert : IsSemiformula LAct ((3 : ℕ) : V) Pinsert := Sentence.quote_isSemiformula _
lemma shift_Pinsert : shift LAct (Pinsert : V) = Pinsert := shift_quote_sentence _

/-- The code of `sequentLen` (arity 2). -/
noncomputable def PsetLen : V := ⌜Semiformula.lMap emb (↑(sequentLenDef LAct) : ArithmeticSemisentence 2)⌝
lemma isSemiformula_PsetLen : IsSemiformula LAct ((2 : ℕ) : V) PsetLen := Sentence.quote_isSemiformula _
lemma shift_PsetLen : shift LAct (PsetLen : V) = PsetLen := shift_quote_sentence _

/-- The code of `fsetPi` (arity 1). -/
noncomputable def PfsetPi : V := ⌜Semiformula.lMap emb (↑(isFormulaSet LAct).pi : ArithmeticSemisentence 1)⌝
lemma isSemiformula_PfsetPi : IsSemiformula LAct ((1 : ℕ) : V) PfsetPi := Sentence.quote_isSemiformula _
lemma shift_PfsetPi : shift LAct (PfsetPi : V) = PfsetPi := shift_quote_sentence _

/-- The code of `fsetSigma` (arity 1). -/
noncomputable def PfsetSigma : V := ⌜Semiformula.lMap emb (↑(isFormulaSet LAct).sigma : ArithmeticSemisentence 1)⌝
lemma isSemiformula_PfsetSigma : IsSemiformula LAct ((1 : ℕ) : V) PfsetSigma := Sentence.quote_isSemiformula _

/-- The code of `length` (arity 2). -/
noncomputable def Plength : V := ⌜Semiformula.lMap emb (↑lengthDef : ArithmeticSemisentence 2)⌝
lemma isSemiformula_Plength : IsSemiformula LAct ((2 : ℕ) : V) Plength := Sentence.quote_isSemiformula _

/-- The code of `tlvG` (arity 3). -/
noncomputable def PtlvG : V := ⌜Semiformula.lMap emb (↑(termLenVecGraph LAct) : ArithmeticSemisentence 3)⌝
lemma isSemiformula_PtlvG : IsSemiformula LAct ((3 : ℕ) : V) PtlvG := Sentence.quote_isSemiformula _
lemma shift_PtlvG : shift LAct (PtlvG : V) = PtlvG := shift_quote_sentence _

/-- The code of `listSum` (arity 2). -/
noncomputable def PlistSum : V := ⌜Semiformula.lMap emb (↑listSumDef : ArithmeticSemisentence 2)⌝
lemma isSemiformula_PlistSum : IsSemiformula LAct ((2 : ℕ) : V) PlistSum := Sentence.quote_isSemiformula _
lemma shift_PlistSum : shift LAct (PlistSum : V) = PlistSum := shift_quote_sentence _

/-- The code of `binNumeralG` (arity 2). -/
noncomputable def Pbnum : V := ⌜Semiformula.lMap emb (↑binNumeralGraph : ArithmeticSemisentence 2)⌝
lemma isSemiformula_Pbnum : IsSemiformula LAct ((2 : ℕ) : V) Pbnum := Sentence.quote_isSemiformula _
lemma shift_Pbnum : shift LAct (Pbnum : V) = Pbnum := shift_quote_sentence _

/-- The code of `nth` (arity 3). -/
noncomputable def Pnth : V := ⌜Semiformula.lMap emb (↑nthDef : ArithmeticSemisentence 3)⌝
lemma isSemiformula_Pnth : IsSemiformula LAct ((3 : ℕ) : V) Pnth := Sentence.quote_isSemiformula _

/-- The code of `fvarVec` (arity 2). -/
noncomputable def PfvarVec : V := ⌜Semiformula.lMap emb (↑fvarVecDef : ArithmeticSemisentence 2)⌝
lemma isSemiformula_PfvarVec : IsSemiformula LAct ((2 : ℕ) : V) PfvarVec := Sentence.quote_isSemiformula _

/-- The code of `tshG` (arity 2). -/
noncomputable def PtshG : V := ⌜Semiformula.lMap emb (↑(termShiftGraph LAct) : ArithmeticSemisentence 2)⌝
lemma isSemiformula_PtshG : IsSemiformula LAct ((2 : ℕ) : V) PtshG := Sentence.quote_isSemiformula _

/-- The code of `tsG` (arity 3). -/
noncomputable def PtsG : V := ⌜Semiformula.lMap emb (↑(termSubstGraph LAct) : ArithmeticSemisentence 3)⌝
lemma isSemiformula_PtsG : IsSemiformula LAct ((3 : ℕ) : V) PtsG := Sentence.quote_isSemiformula _

/-- The code of `tbshG` (arity 2). -/
noncomputable def PtbshG : V := ⌜Semiformula.lMap emb (↑(termBShiftGraph LAct) : ArithmeticSemisentence 2)⌝
lemma isSemiformula_PtbshG : IsSemiformula LAct ((2 : ℕ) : V) PtbshG := Sentence.quote_isSemiformula _

/-- The code of `alls` (arity 3). -/
noncomputable def Palls : V := ⌜Semiformula.lMap emb (↑qqAllsDef : ArithmeticSemisentence 3)⌝
lemma isSemiformula_Palls : IsSemiformula LAct ((3 : ℕ) : V) Palls := Sentence.quote_isSemiformula _

/-- The code of `axL` (arity 3). -/
noncomputable def PaxL : V := ⌜Semiformula.lMap emb (↑axLGraph : ArithmeticSemisentence 3)⌝
lemma isSemiformula_PaxL : IsSemiformula LAct ((3 : ℕ) : V) PaxL := Sentence.quote_isSemiformula _
lemma shift_PaxL : shift LAct (PaxL : V) = PaxL := shift_quote_sentence _

/-- The code of `verumIntro` (arity 2). -/
noncomputable def PverumIntro : V := ⌜Semiformula.lMap emb (↑verumIntroGraph : ArithmeticSemisentence 2)⌝
lemma isSemiformula_PverumIntro : IsSemiformula LAct ((2 : ℕ) : V) PverumIntro := Sentence.quote_isSemiformula _
lemma shift_PverumIntro : shift LAct (PverumIntro : V) = PverumIntro := shift_quote_sentence _

/-- The code of `andIntro` (arity 6). -/
noncomputable def PandIntro : V := ⌜Semiformula.lMap emb (↑andIntroGraph : ArithmeticSemisentence 6)⌝
lemma isSemiformula_PandIntro : IsSemiformula LAct ((6 : ℕ) : V) PandIntro := Sentence.quote_isSemiformula _
lemma shift_PandIntro : shift LAct (PandIntro : V) = PandIntro := shift_quote_sentence _

/-- The code of `orIntro` (arity 5). -/
noncomputable def PorIntro : V := ⌜Semiformula.lMap emb (↑orIntroGraph : ArithmeticSemisentence 5)⌝
lemma isSemiformula_PorIntro : IsSemiformula LAct ((5 : ℕ) : V) PorIntro := Sentence.quote_isSemiformula _
lemma shift_PorIntro : shift LAct (PorIntro : V) = PorIntro := shift_quote_sentence _

/-- The code of `allIntro` (arity 4). -/
noncomputable def PallIntro : V := ⌜Semiformula.lMap emb (↑allIntroGraph : ArithmeticSemisentence 4)⌝
lemma isSemiformula_PallIntro : IsSemiformula LAct ((4 : ℕ) : V) PallIntro := Sentence.quote_isSemiformula _
lemma shift_PallIntro : shift LAct (PallIntro : V) = PallIntro := shift_quote_sentence _

/-- The code of `exsIntro` (arity 5). -/
noncomputable def PexsIntro : V := ⌜Semiformula.lMap emb (↑exsIntroGraph : ArithmeticSemisentence 5)⌝
lemma isSemiformula_PexsIntro : IsSemiformula LAct ((5 : ℕ) : V) PexsIntro := Sentence.quote_isSemiformula _
lemma shift_PexsIntro : shift LAct (PexsIntro : V) = PexsIntro := shift_quote_sentence _

/-- The code of `wkRule` (arity 3). -/
noncomputable def PwkRule : V := ⌜Semiformula.lMap emb (↑wkRuleGraph : ArithmeticSemisentence 3)⌝
lemma isSemiformula_PwkRule : IsSemiformula LAct ((3 : ℕ) : V) PwkRule := Sentence.quote_isSemiformula _
lemma shift_PwkRule : shift LAct (PwkRule : V) = PwkRule := shift_quote_sentence _

/-- The code of `shiftRule` (arity 3). -/
noncomputable def PshiftRule : V := ⌜Semiformula.lMap emb (↑shiftRuleGraph : ArithmeticSemisentence 3)⌝
lemma isSemiformula_PshiftRule : IsSemiformula LAct ((3 : ℕ) : V) PshiftRule := Sentence.quote_isSemiformula _
lemma shift_PshiftRule : shift LAct (PshiftRule : V) = PshiftRule := shift_quote_sentence _

/-- The code of `cutRule` (arity 5). -/
noncomputable def PcutRule : V := ⌜Semiformula.lMap emb (↑cutRuleGraph : ArithmeticSemisentence 5)⌝
lemma isSemiformula_PcutRule : IsSemiformula LAct ((5 : ℕ) : V) PcutRule := Sentence.quote_isSemiformula _
lemma shift_PcutRule : shift LAct (PcutRule : V) = PcutRule := shift_quote_sentence _

/-- The code of `axm` (arity 3). -/
noncomputable def Paxm : V := ⌜Semiformula.lMap emb (↑axmGraph : ArithmeticSemisentence 3)⌝
lemma isSemiformula_Paxm : IsSemiformula LAct ((3 : ℕ) : V) Paxm := Sentence.quote_isSemiformula _
lemma shift_Paxm : shift LAct (Paxm : V) = Paxm := shift_quote_sentence _

lemma shift_Pderiv : shift LAct (Pderiv : V) = Pderiv := shift_quote_sentence _

lemma shift_Pdlen : shift LAct (Pdlen : V) = Pdlen := shift_quote_sentence _

/-- The code of `proofLenDef` (arity 2). -/
noncomputable def PdlenDef : V := ⌜Semiformula.lMap emb (↑(proofLenDef TAct) : ArithmeticSemisentence 2)⌝
lemma isSemiformula_PdlenDef : IsSemiformula LAct ((2 : ℕ) : V) PdlenDef := Sentence.quote_isSemiformula _

/-- The code of `proof` (arity 2). -/
noncomputable def Pproof : V := ⌜Semiformula.lMap emb (↑(proof TAct).sigma : ArithmeticSemisentence 2)⌝
lemma isSemiformula_Pproof : IsSemiformula LAct ((2 : ℕ) : V) Pproof := Sentence.quote_isSemiformula _

/-- The code of `instBG` (arity 3). -/
noncomputable def PinstB : V := ⌜Semiformula.lMap emb (↑instBGraph : ArithmeticSemisentence 3)⌝
lemma isSemiformula_PinstB : IsSemiformula LAct ((3 : ℕ) : V) PinstB := Sentence.quote_isSemiformula _
lemma shift_PinstB : shift LAct (PinstB : V) = PinstB := shift_quote_sentence _

/-- The code of `gG` (arity 2). -/
noncomputable def Pg : V := ⌜Semiformula.lMap emb (↑gGraph : ArithmeticSemisentence 2)⌝
lemma isSemiformula_Pg : IsSemiformula LAct ((2 : ℕ) : V) Pg := Sentence.quote_isSemiformula _

lemma shift_Ple : shift LAct (Ple : V) = Ple := shift_quote_sentence _

/-- The code of `tbshvG` (arity 3). -/
noncomputable def PtbshvG : V := ⌜Semiformula.lMap emb (↑(termBShiftVecGraph LAct) : ArithmeticSemisentence 3)⌝
lemma isSemiformula_PtbshvG : IsSemiformula LAct ((3 : ℕ) : V) PtbshvG := Sentence.quote_isSemiformula _

/-! ### The facts: `subst (listToVec [witnesses]) P` in the predicate's own variable order -/

noncomputable def eqFactB (a b : V) : V := subst LAct (listToVec [a, b]) PeqB
lemma isFormula_eqFactB {a b : V} (ha : IsSemiterm LAct 0 a) (hb : IsSemiterm LAct 0 b) : IsFormula LAct (eqFactB a b) :=
  isFormula_fact isSemiformula_PeqB _ rfl (List.forall_mem_cons.mpr ⟨ha, List.forall_mem_cons.mpr ⟨hb, List.forall_mem_nil _⟩⟩)
lemma shift_eqFactB {a b : V} (ha : IsSemiterm LAct 0 a) (hb : IsSemiterm LAct 0 b) :
    shift LAct (eqFactB a b) = eqFactB (termShift LAct a) (termShift LAct b) := by
  unfold eqFactB
  rw [shift_subst_listToVec [a, b] isSemiformula_PeqB shift_PeqB (n := 0) (List.forall_mem_cons.mpr ⟨ha, List.forall_mem_cons.mpr ⟨hb, List.forall_mem_nil _⟩⟩)]
  rfl

noncomputable def lenFact (l p : V) : V := subst LAct (listToVec [l, p]) PflenG
lemma isFormula_lenFact {l p : V} (hl : IsSemiterm LAct 0 l) (hp : IsSemiterm LAct 0 p) : IsFormula LAct (lenFact l p) :=
  isFormula_fact isSemiformula_PflenG _ rfl (List.forall_mem_cons.mpr ⟨hl, List.forall_mem_cons.mpr ⟨hp, List.forall_mem_nil _⟩⟩)
lemma shift_lenFact {l p : V} (hl : IsSemiterm LAct 0 l) (hp : IsSemiterm LAct 0 p) :
    shift LAct (lenFact l p) = lenFact (termShift LAct l) (termShift LAct p) := by
  unfold lenFact
  rw [shift_subst_listToVec [l, p] isSemiformula_PflenG shift_PflenG (n := 0) (List.forall_mem_cons.mpr ⟨hl, List.forall_mem_cons.mpr ⟨hp, List.forall_mem_nil _⟩⟩)]
  rfl

noncomputable def termLenMetaFact (l t : V) : V := subst LAct (listToVec [l, t]) PtlenG
lemma isFormula_termLenMetaFact {l t : V} (hl : IsSemiterm LAct 0 l) (ht : IsSemiterm LAct 0 t) : IsFormula LAct (termLenMetaFact l t) :=
  isFormula_fact isSemiformula_PtlenG _ rfl (List.forall_mem_cons.mpr ⟨hl, List.forall_mem_cons.mpr ⟨ht, List.forall_mem_nil _⟩⟩)
lemma shift_termLenMetaFact {l t : V} (hl : IsSemiterm LAct 0 l) (ht : IsSemiterm LAct 0 t) :
    shift LAct (termLenMetaFact l t) = termLenMetaFact (termShift LAct l) (termShift LAct t) := by
  unfold termLenMetaFact
  rw [shift_subst_listToVec [l, t] isSemiformula_PtlenG shift_PtlenG (n := 0) (List.forall_mem_cons.mpr ⟨hl, List.forall_mem_cons.mpr ⟨ht, List.forall_mem_nil _⟩⟩)]
  rfl

noncomputable def memFact (x s : V) : V := subst LAct (listToVec [x, s]) Pmem
lemma isFormula_memFact {x s : V} (hx : IsSemiterm LAct 0 x) (hs : IsSemiterm LAct 0 s) : IsFormula LAct (memFact x s) :=
  isFormula_fact isSemiformula_Pmem _ rfl (List.forall_mem_cons.mpr ⟨hx, List.forall_mem_cons.mpr ⟨hs, List.forall_mem_nil _⟩⟩)
lemma shift_memFact {x s : V} (hx : IsSemiterm LAct 0 x) (hs : IsSemiterm LAct 0 s) :
    shift LAct (memFact x s) = memFact (termShift LAct x) (termShift LAct s) := by
  unfold memFact
  rw [shift_subst_listToVec [x, s] isSemiformula_Pmem shift_Pmem (n := 0) (List.forall_mem_cons.mpr ⟨hx, List.forall_mem_cons.mpr ⟨hs, List.forall_mem_nil _⟩⟩)]
  rfl

lemma shift_fstIdxFact {s e : V} (hs : IsSemiterm LAct 0 s) (he : IsSemiterm LAct 0 e) :
    shift LAct (fstIdxFact s e) = fstIdxFact (termShift LAct s) (termShift LAct e) := by
  unfold fstIdxFact
  rw [shift_subst_listToVec [s, e] isSemiformula_PfstIdx shift_PfstIdx (n := 0) (List.forall_mem_cons.mpr ⟨hs, List.forall_mem_cons.mpr ⟨he, List.forall_mem_nil _⟩⟩)]
  rfl

noncomputable def subsetFact (s t : V) : V := subst LAct (listToVec [s, t]) Psubset
lemma isFormula_subsetFact {s t : V} (hs : IsSemiterm LAct 0 s) (ht : IsSemiterm LAct 0 t) : IsFormula LAct (subsetFact s t) :=
  isFormula_fact isSemiformula_Psubset _ rfl (List.forall_mem_cons.mpr ⟨hs, List.forall_mem_cons.mpr ⟨ht, List.forall_mem_nil _⟩⟩)
lemma shift_subsetFact {s t : V} (hs : IsSemiterm LAct 0 s) (ht : IsSemiterm LAct 0 t) :
    shift LAct (subsetFact s t) = subsetFact (termShift LAct s) (termShift LAct t) := by
  unfold subsetFact
  rw [shift_subst_listToVec [s, t] isSemiformula_Psubset shift_Psubset (n := 0) (List.forall_mem_cons.mpr ⟨hs, List.forall_mem_cons.mpr ⟨ht, List.forall_mem_nil _⟩⟩)]
  rfl

noncomputable def setShiftFact (t s : V) : V := subst LAct (listToVec [t, s]) PsetShiftG
lemma isFormula_setShiftFact {t s : V} (ht : IsSemiterm LAct 0 t) (hs : IsSemiterm LAct 0 s) : IsFormula LAct (setShiftFact t s) :=
  isFormula_fact isSemiformula_PsetShiftG _ rfl (List.forall_mem_cons.mpr ⟨ht, List.forall_mem_cons.mpr ⟨hs, List.forall_mem_nil _⟩⟩)
lemma shift_setShiftFact {t s : V} (ht : IsSemiterm LAct 0 t) (hs : IsSemiterm LAct 0 s) :
    shift LAct (setShiftFact t s) = setShiftFact (termShift LAct t) (termShift LAct s) := by
  unfold setShiftFact
  rw [shift_subst_listToVec [t, s] isSemiformula_PsetShiftG shift_PsetShiftG (n := 0) (List.forall_mem_cons.mpr ⟨ht, List.forall_mem_cons.mpr ⟨hs, List.forall_mem_nil _⟩⟩)]
  rfl

noncomputable def insFact (t x s : V) : V := subst LAct (listToVec [t, x, s]) Pinsert
lemma isFormula_insFact {t x s : V} (ht : IsSemiterm LAct 0 t) (hx : IsSemiterm LAct 0 x) (hs : IsSemiterm LAct 0 s) : IsFormula LAct (insFact t x s) :=
  isFormula_fact isSemiformula_Pinsert _ rfl (List.forall_mem_cons.mpr ⟨ht, List.forall_mem_cons.mpr ⟨hx, List.forall_mem_cons.mpr ⟨hs, List.forall_mem_nil _⟩⟩⟩)
lemma shift_insFact {t x s : V} (ht : IsSemiterm LAct 0 t) (hx : IsSemiterm LAct 0 x) (hs : IsSemiterm LAct 0 s) :
    shift LAct (insFact t x s) = insFact (termShift LAct t) (termShift LAct x) (termShift LAct s) := by
  unfold insFact
  rw [shift_subst_listToVec [t, x, s] isSemiformula_Pinsert shift_Pinsert (n := 0) (List.forall_mem_cons.mpr ⟨ht, List.forall_mem_cons.mpr ⟨hx, List.forall_mem_cons.mpr ⟨hs, List.forall_mem_nil _⟩⟩⟩)]
  rfl

noncomputable def sequentLenFact (l s : V) : V := subst LAct (listToVec [l, s]) PsetLen
lemma isFormula_sequentLenFact {l s : V} (hl : IsSemiterm LAct 0 l) (hs : IsSemiterm LAct 0 s) : IsFormula LAct (sequentLenFact l s) :=
  isFormula_fact isSemiformula_PsetLen _ rfl (List.forall_mem_cons.mpr ⟨hl, List.forall_mem_cons.mpr ⟨hs, List.forall_mem_nil _⟩⟩)
lemma shift_sequentLenFact {l s : V} (hl : IsSemiterm LAct 0 l) (hs : IsSemiterm LAct 0 s) :
    shift LAct (sequentLenFact l s) = sequentLenFact (termShift LAct l) (termShift LAct s) := by
  unfold sequentLenFact
  rw [shift_subst_listToVec [l, s] isSemiformula_PsetLen shift_PsetLen (n := 0) (List.forall_mem_cons.mpr ⟨hl, List.forall_mem_cons.mpr ⟨hs, List.forall_mem_nil _⟩⟩)]
  rfl

noncomputable def fsetPiFact (s : V) : V := subst LAct (listToVec [s]) PfsetPi
lemma isFormula_fsetPiFact {s : V} (hs : IsSemiterm LAct 0 s) : IsFormula LAct (fsetPiFact s) :=
  isFormula_fact isSemiformula_PfsetPi _ rfl (List.forall_mem_cons.mpr ⟨hs, List.forall_mem_nil _⟩)
lemma shift_fsetPiFact {s : V} (hs : IsSemiterm LAct 0 s) :
    shift LAct (fsetPiFact s) = fsetPiFact (termShift LAct s) := by
  unfold fsetPiFact
  rw [shift_subst_listToVec [s] isSemiformula_PfsetPi shift_PfsetPi (n := 0) (List.forall_mem_cons.mpr ⟨hs, List.forall_mem_nil _⟩)]
  rfl

noncomputable def fsetSigmaFact (s : V) : V := subst LAct (listToVec [s]) PfsetSigma

noncomputable def lengthFact (l k : V) : V := subst LAct (listToVec [l, k]) Plength
lemma isFormula_lengthFact {l k : V} (hl : IsSemiterm LAct 0 l) (hk : IsSemiterm LAct 0 k) : IsFormula LAct (lengthFact l k) :=
  isFormula_fact isSemiformula_Plength _ rfl (List.forall_mem_cons.mpr ⟨hl, List.forall_mem_cons.mpr ⟨hk, List.forall_mem_nil _⟩⟩)
lemma formulaLen_lengthFact_le {B : V} (hB : 1 ≤ B) {l k : V} (hl : IsSemiterm LAct 0 l) (hk : IsSemiterm LAct 0 k) (hll : termLen LAct l ≤ B) (hlk : termLen LAct k ≤ B) :
    formulaLen LAct (lengthFact l k) ≤ formulaLen LAct (Plength : V) * B :=
  formulaLen_fact_le hB isSemiformula_Plength _ rfl (List.forall_mem_cons.mpr ⟨⟨hl, hll⟩, List.forall_mem_cons.mpr ⟨⟨hk, hlk⟩, List.forall_mem_nil _⟩⟩)

noncomputable def tlvFact (M k v : V) : V := subst LAct (listToVec [M, k, v]) PtlvG
lemma isFormula_tlvFact {M k v : V} (hM : IsSemiterm LAct 0 M) (hk : IsSemiterm LAct 0 k) (hv : IsSemiterm LAct 0 v) : IsFormula LAct (tlvFact M k v) :=
  isFormula_fact isSemiformula_PtlvG _ rfl (List.forall_mem_cons.mpr ⟨hM, List.forall_mem_cons.mpr ⟨hk, List.forall_mem_cons.mpr ⟨hv, List.forall_mem_nil _⟩⟩⟩)
lemma shift_tlvFact {M k v : V} (hM : IsSemiterm LAct 0 M) (hk : IsSemiterm LAct 0 k) (hv : IsSemiterm LAct 0 v) :
    shift LAct (tlvFact M k v) = tlvFact (termShift LAct M) (termShift LAct k) (termShift LAct v) := by
  unfold tlvFact
  rw [shift_subst_listToVec [M, k, v] isSemiformula_PtlvG shift_PtlvG (n := 0) (List.forall_mem_cons.mpr ⟨hM, List.forall_mem_cons.mpr ⟨hk, List.forall_mem_cons.mpr ⟨hv, List.forall_mem_nil _⟩⟩⟩)]
  rfl

noncomputable def listSumFact (s M : V) : V := subst LAct (listToVec [s, M]) PlistSum
lemma isFormula_listSumFact {s M : V} (hs : IsSemiterm LAct 0 s) (hM : IsSemiterm LAct 0 M) : IsFormula LAct (listSumFact s M) :=
  isFormula_fact isSemiformula_PlistSum _ rfl (List.forall_mem_cons.mpr ⟨hs, List.forall_mem_cons.mpr ⟨hM, List.forall_mem_nil _⟩⟩)
lemma shift_listSumFact {s M : V} (hs : IsSemiterm LAct 0 s) (hM : IsSemiterm LAct 0 M) :
    shift LAct (listSumFact s M) = listSumFact (termShift LAct s) (termShift LAct M) := by
  unfold listSumFact
  rw [shift_subst_listToVec [s, M] isSemiformula_PlistSum shift_PlistSum (n := 0) (List.forall_mem_cons.mpr ⟨hs, List.forall_mem_cons.mpr ⟨hM, List.forall_mem_nil _⟩⟩)]
  rfl

noncomputable def binNumeralFact (t k : V) : V := subst LAct (listToVec [t, k]) Pbnum
lemma isFormula_binNumeralFact {t k : V} (ht : IsSemiterm LAct 0 t) (hk : IsSemiterm LAct 0 k) : IsFormula LAct (binNumeralFact t k) :=
  isFormula_fact isSemiformula_Pbnum _ rfl (List.forall_mem_cons.mpr ⟨ht, List.forall_mem_cons.mpr ⟨hk, List.forall_mem_nil _⟩⟩)

noncomputable def nthFact (e w i : V) : V := subst LAct (listToVec [e, w, i]) Pnth

noncomputable def fvarVecFact (fv m : V) : V := subst LAct (listToVec [fv, m]) PfvarVec

noncomputable def tshFact (t2 t : V) : V := subst LAct (listToVec [t2, t]) PtshG

noncomputable def tsFact (e w t : V) : V := subst LAct (listToVec [e, w, t]) PtsG

noncomputable def tbshFact (e2 e : V) : V := subst LAct (listToVec [e2, e]) PtbshG

noncomputable def allsFact (p b m : V) : V := subst LAct (listToVec [p, b, m]) Palls

noncomputable def axLFact (e s p : V) : V := subst LAct (listToVec [e, s, p]) PaxL

noncomputable def verumIntroFact (e s : V) : V := subst LAct (listToVec [e, s]) PverumIntro

noncomputable def andIntroFact (e s p q dp dq : V) : V := subst LAct (listToVec [e, s, p, q, dp, dq]) PandIntro

noncomputable def orIntroFact (e s p q d : V) : V := subst LAct (listToVec [e, s, p, q, d]) PorIntro

noncomputable def allIntroFact (e s p d : V) : V := subst LAct (listToVec [e, s, p, d]) PallIntro

noncomputable def exsIntroFact (e s p t d : V) : V := subst LAct (listToVec [e, s, p, t, d]) PexsIntro

noncomputable def wkRuleFact (e s d : V) : V := subst LAct (listToVec [e, s, d]) PwkRule

noncomputable def shiftRuleFact (e s d : V) : V := subst LAct (listToVec [e, s, d]) PshiftRule

noncomputable def cutRuleFact (e s p d1 d2 : V) : V := subst LAct (listToVec [e, s, p, d1, d2]) PcutRule

noncomputable def axmFact (e s p : V) : V := subst LAct (listToVec [e, s, p]) Paxm

lemma shift_derFact {e : V} (he : IsSemiterm LAct 0 e) :
    shift LAct (derFact e) = derFact (termShift LAct e) := by
  unfold derFact
  rw [shift_subst_listToVec [e] isSemiformula_Pderiv shift_Pderiv (n := 0) (List.forall_mem_cons.mpr ⟨he, List.forall_mem_nil _⟩)]
  rfl

lemma shift_proofLenFact {e n : V} (he : IsSemiterm LAct 0 e) (hn : IsSemiterm LAct 0 n) :
    shift LAct (proofLenFact e n) = proofLenFact (termShift LAct e) (termShift LAct n) := by
  unfold proofLenFact
  rw [shift_subst_listToVec [e, n] isSemiformula_Pdlen shift_Pdlen (n := 0) (List.forall_mem_cons.mpr ⟨he, List.forall_mem_cons.mpr ⟨hn, List.forall_mem_nil _⟩⟩)]
  rfl

noncomputable def proofLenDefFact (n d : V) : V := subst LAct (listToVec [n, d]) PdlenDef

noncomputable def proofFact (d g : V) : V := subst LAct (listToVec [d, g]) Pproof

noncomputable def instBFact (g n k : V) : V := subst LAct (listToVec [g, n, k]) PinstB
lemma isFormula_instBFact {g n k : V} (hg : IsSemiterm LAct 0 g) (hn : IsSemiterm LAct 0 n) (hk : IsSemiterm LAct 0 k) : IsFormula LAct (instBFact g n k) :=
  isFormula_fact isSemiformula_PinstB _ rfl (List.forall_mem_cons.mpr ⟨hg, List.forall_mem_cons.mpr ⟨hn, List.forall_mem_cons.mpr ⟨hk, List.forall_mem_nil _⟩⟩⟩)
lemma shift_instBFact {g n k : V} (hg : IsSemiterm LAct 0 g) (hn : IsSemiterm LAct 0 n) (hk : IsSemiterm LAct 0 k) :
    shift LAct (instBFact g n k) = instBFact (termShift LAct g) (termShift LAct n) (termShift LAct k) := by
  unfold instBFact
  rw [shift_subst_listToVec [g, n, k] isSemiformula_PinstB shift_PinstB (n := 0) (List.forall_mem_cons.mpr ⟨hg, List.forall_mem_cons.mpr ⟨hn, List.forall_mem_cons.mpr ⟨hk, List.forall_mem_nil _⟩⟩⟩)]
  rfl

noncomputable def gFact (a k : V) : V := subst LAct (listToVec [a, k]) Pg

lemma shift_leFact {n u : V} (hn : IsSemiterm LAct 0 n) (hu : IsSemiterm LAct 0 u) :
    shift LAct (leFact n u) = leFact (termShift LAct n) (termShift LAct u) := by
  unfold leFact
  rw [shift_subst_listToVec [n, u] isSemiformula_Ple shift_Ple (n := 0) (List.forall_mem_cons.mpr ⟨hn, List.forall_mem_cons.mpr ⟨hu, List.forall_mem_nil _⟩⟩)]
  rfl

noncomputable def tbshvFact (u k v : V) : V := subst LAct (listToVec [u, k, v]) PtbshvG

end facts

/-! ## 3. The rows: pieces, row-shape, formula-ness, instantiation -/

section rows

/-! ## A. Copy-in: equality and the congruence rows (§3.3) -/

/-! ### `eqTotal` — `“x. …”`, `m = 1` -/

noncomputable def row_eqTotal_as : List V := []
noncomputable def row_eqTotal_body : V := subst LAct (listToVec [bv 0, bv 1]) PeqB
noncomputable def row_eqTotal_R : V := row_eqTotal_body
noncomputable def row_eqTotal_c : V := ^∃ row_eqTotal_R

theorem quote_row_eqTotal : (⌜Semiformula.lMap emb eqTotalB⌝ : V) = impChain LAct row_eqTotal_as row_eqTotal_c := by
  unfold eqTotalB row_eqTotal_as row_eqTotal_c row_eqTotal_R row_eqTotal_body PeqB
  all_goals row_shapeB

lemma isSemiformula_eqTotal_R : IsSemiformula LAct ((2 : ℕ) : V) row_eqTotal_R := by
  unfold row_eqTotal_R row_eqTotal_body
  exact isSemiformula_substRow isSemiformula_PeqB _ (by rfl) (by row_entriesB)
lemma row_eqTotal_R_eq : (row_eqTotal_R : V) = exsIter 0 row_eqTotal_body := rfl

/-- `eqTotal` at the witnesses `[wx]` (the DSL variables right-to-left). -/
lemma inst_eqTotal {wx : V} (hwx : IsSemiterm LAct 0 wx) :
    row_eqTotal_as.map (instOuter LAct [wx]) = [] ∧
    freeIter LAct 1 (instOuterAt LAct 1 [wx] row_eqTotal_body) = eqFactB (^&((0 : ℕ) : V)) (termShift LAct wx) := by
  have hes : ∀ e ∈ ([wx] : List V), IsSemiterm LAct 0 e := (List.forall_mem_cons.mpr ⟨hwx, List.forall_mem_nil _⟩)
  unfold row_eqTotal_as row_eqTotal_body
  simp only [List.map_cons, List.map_nil]
  refine ⟨by ((try row_entries_simpB); row_finish), ?_⟩
  · rw [instOuterAt_subst_listToVec 1 _ isSemiformula_PeqB (by rfl) _ hes (by row_entriesB)]
    row_entries_simpB
    rw [freeIter_subst_listToVec' 1 _ isSemiformula_PeqB shift_PeqB (by rfl) (by row_entriesB)]
    simp only [List.map_cons, List.map_nil]
    rw [freeIterT_bv0 1 0 (by norm_num), freeIterT_closed 0 hwx 1]
    try rfl

/-! ### `eqRefl` — `“x. …”`, `m = 1` -/

noncomputable def row_eqRefl_as : List V := []
noncomputable def row_eqRefl_c : V := subst LAct (listToVec [bv 0, bv 0]) PeqB

theorem quote_row_eqRefl : (⌜Semiformula.lMap emb eqReflB⌝ : V) = impChain LAct row_eqRefl_as row_eqRefl_c := by
  unfold eqReflB row_eqRefl_as row_eqRefl_c PeqB
  all_goals row_shapeB

lemma isSemiformula_eqRefl_c : IsSemiformula LAct ((1 : ℕ) : V) row_eqRefl_c := by
  unfold row_eqRefl_c
  exact isSemiformula_substRow isSemiformula_PeqB _ (by rfl) (by row_entriesB)

/-- `eqRefl` at the witnesses `[wx]` (the DSL variables right-to-left). -/
lemma inst_eqRefl {wx : V} (hwx : IsSemiterm LAct 0 wx) :
    row_eqRefl_as.map (instOuter LAct [wx]) = [] ∧
    instOuter LAct [wx] row_eqRefl_c = eqFactB wx wx := by
  have hes : ∀ e ∈ ([wx] : List V), IsSemiterm LAct 0 e := (List.forall_mem_cons.mpr ⟨hwx, List.forall_mem_nil _⟩)
  unfold row_eqRefl_as row_eqRefl_c
  simp only [List.map_cons, List.map_nil]
  rw [instOuter_subst_listToVec _ isSemiformula_PeqB (by rfl) _ hes (by row_entriesB)]
  all_goals try row_entries_simpB
  row_finish

/-! ### `eqSymm` — `“y x. …”`, `m = 2` -/

noncomputable def row_eqSymm_as : List V := [subst LAct (listToVec [bv 1, bv 0]) PeqB]
noncomputable def row_eqSymm_c : V := subst LAct (listToVec [bv 0, bv 1]) PeqB

theorem quote_row_eqSymm : (⌜Semiformula.lMap emb eqSymmB⌝ : V) = impChain LAct row_eqSymm_as row_eqSymm_c := by
  unfold eqSymmB row_eqSymm_as row_eqSymm_c PeqB
  all_goals row_shapeB

lemma isSemiformula_eqSymm_c : IsSemiformula LAct ((2 : ℕ) : V) row_eqSymm_c := by
  unfold row_eqSymm_c
  exact isSemiformula_substRow isSemiformula_PeqB _ (by rfl) (by row_entriesB)

/-- `eqSymm` at the witnesses `[wx, wy]` (the DSL variables right-to-left). -/
lemma inst_eqSymm {wx wy : V} (hwx : IsSemiterm LAct 0 wx) (hwy : IsSemiterm LAct 0 wy) :
    row_eqSymm_as.map (instOuter LAct [wx, wy]) = [eqFactB wx wy] ∧
    instOuter LAct [wx, wy] row_eqSymm_c = eqFactB wy wx := by
  have hes : ∀ e ∈ ([wx, wy] : List V), IsSemiterm LAct 0 e := (List.forall_mem_cons.mpr ⟨hwx, List.forall_mem_cons.mpr ⟨hwy, List.forall_mem_nil _⟩⟩)
  unfold row_eqSymm_as row_eqSymm_c
  simp only [List.map_cons, List.map_nil]
  rw [instOuter_subst_listToVec _ isSemiformula_PeqB (by rfl) _ hes (by row_entriesB), instOuter_subst_listToVec _ isSemiformula_PeqB (by rfl) _ hes (by row_entriesB)]
  all_goals try row_entries_simpB
  row_finish

/-! ### `eqTrans` — `“z y x. …”`, `m = 3` -/

noncomputable def row_eqTrans_as : List V := [subst LAct (listToVec [bv 2, bv 1]) PeqB, subst LAct (listToVec [bv 1, bv 0]) PeqB]
noncomputable def row_eqTrans_c : V := subst LAct (listToVec [bv 2, bv 0]) PeqB

theorem quote_row_eqTrans : (⌜Semiformula.lMap emb eqTransB⌝ : V) = impChain LAct row_eqTrans_as row_eqTrans_c := by
  unfold eqTransB row_eqTrans_as row_eqTrans_c PeqB
  all_goals row_shapeB

lemma isSemiformula_eqTrans_c : IsSemiformula LAct ((3 : ℕ) : V) row_eqTrans_c := by
  unfold row_eqTrans_c
  exact isSemiformula_substRow isSemiformula_PeqB _ (by rfl) (by row_entriesB)

/-- `eqTrans` at the witnesses `[wx, wy, wz]` (the DSL variables right-to-left). -/
lemma inst_eqTrans {wx wy wz : V} (hwx : IsSemiterm LAct 0 wx) (hwy : IsSemiterm LAct 0 wy) (hwz : IsSemiterm LAct 0 wz) :
    row_eqTrans_as.map (instOuter LAct [wx, wy, wz]) = [eqFactB wx wy, eqFactB wy wz] ∧
    instOuter LAct [wx, wy, wz] row_eqTrans_c = eqFactB wx wz := by
  have hes : ∀ e ∈ ([wx, wy, wz] : List V), IsSemiterm LAct 0 e := (List.forall_mem_cons.mpr ⟨hwx, List.forall_mem_cons.mpr ⟨hwy, List.forall_mem_cons.mpr ⟨hwz, List.forall_mem_nil _⟩⟩⟩)
  unfold row_eqTrans_as row_eqTrans_c
  simp only [List.map_cons, List.map_nil]
  rw [instOuter_subst_listToVec _ isSemiformula_PeqB (by rfl) _ hes (by row_entriesB), instOuter_subst_listToVec _ isSemiformula_PeqB (by rfl) _ hes (by row_entriesB), instOuter_subst_listToVec _ isSemiformula_PeqB (by rfl) _ hes (by row_entriesB)]
  all_goals try row_entries_simpB
  row_finish

/-! ### `congPi` — `“y x n. …”`, `m = 3` -/

noncomputable def row_congPi_as : List V := [subst LAct (listToVec [bv 0, bv 1]) PeqB, subst LAct (listToVec [bv 2, bv 1]) Ppi]
noncomputable def row_congPi_c : V := subst LAct (listToVec [bv 2, bv 0]) Psigma

theorem quote_row_congPi : (⌜Semiformula.lMap emb congPiB⌝ : V) = impChain LAct row_congPi_as row_congPi_c := by
  unfold congPiB row_congPi_as row_congPi_c PeqB Ppi Psigma
  all_goals row_shapeB

lemma isSemiformula_congPi_c : IsSemiformula LAct ((3 : ℕ) : V) row_congPi_c := by
  unfold row_congPi_c
  exact isSemiformula_substRow isSemiformula_Psigma _ (by rfl) (by row_entriesB)

/-- `congPi` at the witnesses `[wn, wx, wy]` (the DSL variables right-to-left). -/
lemma inst_congPi {wn wx wy : V} (hwn : IsSemiterm LAct 0 wn) (hwx : IsSemiterm LAct 0 wx) (hwy : IsSemiterm LAct 0 wy) :
    row_congPi_as.map (instOuter LAct [wn, wx, wy]) = [eqFactB wy wx, piFact wn wx] ∧
    instOuter LAct [wn, wx, wy] row_congPi_c = sigmaFact wn wy := by
  have hes : ∀ e ∈ ([wn, wx, wy] : List V), IsSemiterm LAct 0 e := (List.forall_mem_cons.mpr ⟨hwn, List.forall_mem_cons.mpr ⟨hwx, List.forall_mem_cons.mpr ⟨hwy, List.forall_mem_nil _⟩⟩⟩)
  unfold row_congPi_as row_congPi_c
  simp only [List.map_cons, List.map_nil]
  rw [instOuter_subst_listToVec _ isSemiformula_PeqB (by rfl) _ hes (by row_entriesB), instOuter_subst_listToVec _ isSemiformula_Ppi (by rfl) _ hes (by row_entriesB), instOuter_subst_listToVec _ isSemiformula_Psigma (by rfl) _ hes (by row_entriesB)]
  all_goals try row_entries_simpB
  row_finish

/-! ### `congTPi` — `“y x n. …”`, `m = 3` -/

noncomputable def row_congTPi_as : List V := [subst LAct (listToVec [bv 0, bv 1]) PeqB, subst LAct (listToVec [bv 2, bv 1]) PtPi]
noncomputable def row_congTPi_c : V := subst LAct (listToVec [bv 2, bv 0]) PtSigma

theorem quote_row_congTPi : (⌜Semiformula.lMap emb congTPiB⌝ : V) = impChain LAct row_congTPi_as row_congTPi_c := by
  unfold congTPiB row_congTPi_as row_congTPi_c PeqB PtPi PtSigma
  all_goals row_shapeB

lemma isSemiformula_congTPi_c : IsSemiformula LAct ((3 : ℕ) : V) row_congTPi_c := by
  unfold row_congTPi_c
  exact isSemiformula_substRow isSemiformula_PtSigma _ (by rfl) (by row_entriesB)

/-- `congTPi` at the witnesses `[wn, wx, wy]` (the DSL variables right-to-left). -/
lemma inst_congTPi {wn wx wy : V} (hwn : IsSemiterm LAct 0 wn) (hwx : IsSemiterm LAct 0 wx) (hwy : IsSemiterm LAct 0 wy) :
    row_congTPi_as.map (instOuter LAct [wn, wx, wy]) = [eqFactB wy wx, tPiFact wn wx] ∧
    instOuter LAct [wn, wx, wy] row_congTPi_c = tSigmaFact wn wy := by
  have hes : ∀ e ∈ ([wn, wx, wy] : List V), IsSemiterm LAct 0 e := (List.forall_mem_cons.mpr ⟨hwn, List.forall_mem_cons.mpr ⟨hwx, List.forall_mem_cons.mpr ⟨hwy, List.forall_mem_nil _⟩⟩⟩)
  unfold row_congTPi_as row_congTPi_c
  simp only [List.map_cons, List.map_nil]
  rw [instOuter_subst_listToVec _ isSemiformula_PeqB (by rfl) _ hes (by row_entriesB), instOuter_subst_listToVec _ isSemiformula_PtPi (by rfl) _ hes (by row_entriesB), instOuter_subst_listToVec _ isSemiformula_PtSigma (by rfl) _ hes (by row_entriesB)]
  all_goals try row_entries_simpB
  row_finish

/-! ### `congTvPi` — `“y x n k. …”`, `m = 4` -/

noncomputable def row_congTvPi_as : List V := [subst LAct (listToVec [bv 0, bv 1]) PeqB, subst LAct (listToVec [bv 3, bv 2, bv 1]) PtvPi]
noncomputable def row_congTvPi_c : V := subst LAct (listToVec [bv 3, bv 2, bv 0]) PtvSigma

theorem quote_row_congTvPi : (⌜Semiformula.lMap emb congTvPiB⌝ : V) = impChain LAct row_congTvPi_as row_congTvPi_c := by
  unfold congTvPiB row_congTvPi_as row_congTvPi_c PeqB PtvPi PtvSigma
  all_goals row_shapeB

lemma isSemiformula_congTvPi_c : IsSemiformula LAct ((4 : ℕ) : V) row_congTvPi_c := by
  unfold row_congTvPi_c
  exact isSemiformula_substRow isSemiformula_PtvSigma _ (by rfl) (by row_entriesB)

/-- `congTvPi` at the witnesses `[wk, wn, wx, wy]` (the DSL variables right-to-left). -/
lemma inst_congTvPi {wk wn wx wy : V} (hwk : IsSemiterm LAct 0 wk) (hwn : IsSemiterm LAct 0 wn) (hwx : IsSemiterm LAct 0 wx) (hwy : IsSemiterm LAct 0 wy) :
    row_congTvPi_as.map (instOuter LAct [wk, wn, wx, wy]) = [eqFactB wy wx, tvPiFact wk wn wx] ∧
    instOuter LAct [wk, wn, wx, wy] row_congTvPi_c = tvSigmaFact wk wn wy := by
  have hes : ∀ e ∈ ([wk, wn, wx, wy] : List V), IsSemiterm LAct 0 e := (List.forall_mem_cons.mpr ⟨hwk, List.forall_mem_cons.mpr ⟨hwn, List.forall_mem_cons.mpr ⟨hwx, List.forall_mem_cons.mpr ⟨hwy, List.forall_mem_nil _⟩⟩⟩⟩)
  unfold row_congTvPi_as row_congTvPi_c
  simp only [List.map_cons, List.map_nil]
  rw [instOuter_subst_listToVec _ isSemiformula_PeqB (by rfl) _ hes (by row_entriesB), instOuter_subst_listToVec _ isSemiformula_PtvPi (by rfl) _ hes (by row_entriesB), instOuter_subst_listToVec _ isSemiformula_PtvSigma (by rfl) _ hes (by row_entriesB)]
  all_goals try row_entries_simpB
  row_finish

/-! ### `congUtvPi` — `“y x k. …”`, `m = 3` -/

noncomputable def row_congUtvPi_as : List V := [subst LAct (listToVec [bv 0, bv 1]) PeqB, subst LAct (listToVec [bv 2, bv 1]) PutvPi]
noncomputable def row_congUtvPi_c : V := subst LAct (listToVec [bv 2, bv 0]) PutvSigma

theorem quote_row_congUtvPi : (⌜Semiformula.lMap emb congUtvPiB⌝ : V) = impChain LAct row_congUtvPi_as row_congUtvPi_c := by
  unfold congUtvPiB row_congUtvPi_as row_congUtvPi_c PeqB PutvPi PutvSigma
  all_goals row_shapeB

lemma isSemiformula_congUtvPi_c : IsSemiformula LAct ((3 : ℕ) : V) row_congUtvPi_c := by
  unfold row_congUtvPi_c
  exact isSemiformula_substRow isSemiformula_PutvSigma _ (by rfl) (by row_entriesB)

/-- `congUtvPi` at the witnesses `[wk, wx, wy]` (the DSL variables right-to-left). -/
lemma inst_congUtvPi {wk wx wy : V} (hwk : IsSemiterm LAct 0 wk) (hwx : IsSemiterm LAct 0 wx) (hwy : IsSemiterm LAct 0 wy) :
    row_congUtvPi_as.map (instOuter LAct [wk, wx, wy]) = [eqFactB wy wx, utvPiFact wk wx] ∧
    instOuter LAct [wk, wx, wy] row_congUtvPi_c = utvSigmaFact wk wy := by
  have hes : ∀ e ∈ ([wk, wx, wy] : List V), IsSemiterm LAct 0 e := (List.forall_mem_cons.mpr ⟨hwk, List.forall_mem_cons.mpr ⟨hwx, List.forall_mem_cons.mpr ⟨hwy, List.forall_mem_nil _⟩⟩⟩)
  unfold row_congUtvPi_as row_congUtvPi_c
  simp only [List.map_cons, List.map_nil]
  rw [instOuter_subst_listToVec _ isSemiformula_PeqB (by rfl) _ hes (by row_entriesB), instOuter_subst_listToVec _ isSemiformula_PutvPi (by rfl) _ hes (by row_entriesB), instOuter_subst_listToVec _ isSemiformula_PutvSigma (by rfl) _ hes (by row_entriesB)]
  all_goals try row_entries_simpB
  row_finish

/-! ### `congAnd` — `“q' p' r' q p r. …”`, `m = 6` -/

noncomputable def row_congAnd_as : List V := [subst LAct (listToVec [bv 2, bv 5]) PeqB, subst LAct (listToVec [bv 1, bv 4]) PeqB, subst LAct (listToVec [bv 0, bv 3]) PeqB, subst LAct (listToVec [bv 5, bv 4, bv 3]) Pand]
noncomputable def row_congAnd_c : V := subst LAct (listToVec [bv 2, bv 1, bv 0]) Pand

theorem quote_row_congAnd : (⌜Semiformula.lMap emb congAndB⌝ : V) = impChain LAct row_congAnd_as row_congAnd_c := by
  unfold congAndB row_congAnd_as row_congAnd_c Pand PeqB
  all_goals row_shapeB

lemma isSemiformula_congAnd_c : IsSemiformula LAct ((6 : ℕ) : V) row_congAnd_c := by
  unfold row_congAnd_c
  exact isSemiformula_substRow isSemiformula_Pand _ (by rfl) (by row_entriesB)

/-- `congAnd` at the witnesses `[wr, wp, wq, wrp, wpp, wqp]` (the DSL variables right-to-left). -/
lemma inst_congAnd {wr wp wq wrp wpp wqp : V} (hwr : IsSemiterm LAct 0 wr) (hwp : IsSemiterm LAct 0 wp) (hwq : IsSemiterm LAct 0 wq) (hwrp : IsSemiterm LAct 0 wrp) (hwpp : IsSemiterm LAct 0 wpp) (hwqp : IsSemiterm LAct 0 wqp) :
    row_congAnd_as.map (instOuter LAct [wr, wp, wq, wrp, wpp, wqp]) = [eqFactB wrp wr, eqFactB wpp wp, eqFactB wqp wq, andFact wr wp wq] ∧
    instOuter LAct [wr, wp, wq, wrp, wpp, wqp] row_congAnd_c = andFact wrp wpp wqp := by
  have hes : ∀ e ∈ ([wr, wp, wq, wrp, wpp, wqp] : List V), IsSemiterm LAct 0 e := (List.forall_mem_cons.mpr ⟨hwr, List.forall_mem_cons.mpr ⟨hwp, List.forall_mem_cons.mpr ⟨hwq, List.forall_mem_cons.mpr ⟨hwrp, List.forall_mem_cons.mpr ⟨hwpp, List.forall_mem_cons.mpr ⟨hwqp, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩)
  unfold row_congAnd_as row_congAnd_c
  simp only [List.map_cons, List.map_nil]
  rw [instOuter_subst_listToVec _ isSemiformula_PeqB (by rfl) _ hes (by row_entriesB), instOuter_subst_listToVec _ isSemiformula_PeqB (by rfl) _ hes (by row_entriesB), instOuter_subst_listToVec _ isSemiformula_PeqB (by rfl) _ hes (by row_entriesB), instOuter_subst_listToVec _ isSemiformula_Pand (by rfl) _ hes (by row_entriesB), instOuter_subst_listToVec _ isSemiformula_Pand (by rfl) _ hes (by row_entriesB)]
  all_goals try row_entries_simpB
  row_finish

/-! ### `congOr` — `“q' p' r' q p r. …”`, `m = 6` -/

noncomputable def row_congOr_as : List V := [subst LAct (listToVec [bv 2, bv 5]) PeqB, subst LAct (listToVec [bv 1, bv 4]) PeqB, subst LAct (listToVec [bv 0, bv 3]) PeqB, subst LAct (listToVec [bv 5, bv 4, bv 3]) Por]
noncomputable def row_congOr_c : V := subst LAct (listToVec [bv 2, bv 1, bv 0]) Por

theorem quote_row_congOr : (⌜Semiformula.lMap emb congOrB⌝ : V) = impChain LAct row_congOr_as row_congOr_c := by
  unfold congOrB row_congOr_as row_congOr_c PeqB Por
  all_goals row_shapeB

lemma isSemiformula_congOr_c : IsSemiformula LAct ((6 : ℕ) : V) row_congOr_c := by
  unfold row_congOr_c
  exact isSemiformula_substRow isSemiformula_Por _ (by rfl) (by row_entriesB)

/-- `congOr` at the witnesses `[wr, wp, wq, wrp, wpp, wqp]` (the DSL variables right-to-left). -/
lemma inst_congOr {wr wp wq wrp wpp wqp : V} (hwr : IsSemiterm LAct 0 wr) (hwp : IsSemiterm LAct 0 wp) (hwq : IsSemiterm LAct 0 wq) (hwrp : IsSemiterm LAct 0 wrp) (hwpp : IsSemiterm LAct 0 wpp) (hwqp : IsSemiterm LAct 0 wqp) :
    row_congOr_as.map (instOuter LAct [wr, wp, wq, wrp, wpp, wqp]) = [eqFactB wrp wr, eqFactB wpp wp, eqFactB wqp wq, orFact wr wp wq] ∧
    instOuter LAct [wr, wp, wq, wrp, wpp, wqp] row_congOr_c = orFact wrp wpp wqp := by
  have hes : ∀ e ∈ ([wr, wp, wq, wrp, wpp, wqp] : List V), IsSemiterm LAct 0 e := (List.forall_mem_cons.mpr ⟨hwr, List.forall_mem_cons.mpr ⟨hwp, List.forall_mem_cons.mpr ⟨hwq, List.forall_mem_cons.mpr ⟨hwrp, List.forall_mem_cons.mpr ⟨hwpp, List.forall_mem_cons.mpr ⟨hwqp, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩)
  unfold row_congOr_as row_congOr_c
  simp only [List.map_cons, List.map_nil]
  rw [instOuter_subst_listToVec _ isSemiformula_PeqB (by rfl) _ hes (by row_entriesB), instOuter_subst_listToVec _ isSemiformula_PeqB (by rfl) _ hes (by row_entriesB), instOuter_subst_listToVec _ isSemiformula_PeqB (by rfl) _ hes (by row_entriesB), instOuter_subst_listToVec _ isSemiformula_Por (by rfl) _ hes (by row_entriesB), instOuter_subst_listToVec _ isSemiformula_Por (by rfl) _ hes (by row_entriesB)]
  all_goals try row_entries_simpB
  row_finish

/-! ### `congAll` — `“p' q' p q. …”`, `m = 4` -/

noncomputable def row_congAll_as : List V := [subst LAct (listToVec [bv 1, bv 3]) PeqB, subst LAct (listToVec [bv 0, bv 2]) PeqB, subst LAct (listToVec [bv 3, bv 2]) Pall]
noncomputable def row_congAll_c : V := subst LAct (listToVec [bv 1, bv 0]) Pall

theorem quote_row_congAll : (⌜Semiformula.lMap emb congAllB⌝ : V) = impChain LAct row_congAll_as row_congAll_c := by
  unfold congAllB row_congAll_as row_congAll_c Pall PeqB
  all_goals row_shapeB

lemma isSemiformula_congAll_c : IsSemiformula LAct ((4 : ℕ) : V) row_congAll_c := by
  unfold row_congAll_c
  exact isSemiformula_substRow isSemiformula_Pall _ (by rfl) (by row_entriesB)

/-- `congAll` at the witnesses `[wq, wp, wqp, wpp]` (the DSL variables right-to-left). -/
lemma inst_congAll {wq wp wqp wpp : V} (hwq : IsSemiterm LAct 0 wq) (hwp : IsSemiterm LAct 0 wp) (hwqp : IsSemiterm LAct 0 wqp) (hwpp : IsSemiterm LAct 0 wpp) :
    row_congAll_as.map (instOuter LAct [wq, wp, wqp, wpp]) = [eqFactB wqp wq, eqFactB wpp wp, allFact wq wp] ∧
    instOuter LAct [wq, wp, wqp, wpp] row_congAll_c = allFact wqp wpp := by
  have hes : ∀ e ∈ ([wq, wp, wqp, wpp] : List V), IsSemiterm LAct 0 e := (List.forall_mem_cons.mpr ⟨hwq, List.forall_mem_cons.mpr ⟨hwp, List.forall_mem_cons.mpr ⟨hwqp, List.forall_mem_cons.mpr ⟨hwpp, List.forall_mem_nil _⟩⟩⟩⟩)
  unfold row_congAll_as row_congAll_c
  simp only [List.map_cons, List.map_nil]
  rw [instOuter_subst_listToVec _ isSemiformula_PeqB (by rfl) _ hes (by row_entriesB), instOuter_subst_listToVec _ isSemiformula_PeqB (by rfl) _ hes (by row_entriesB), instOuter_subst_listToVec _ isSemiformula_Pall (by rfl) _ hes (by row_entriesB), instOuter_subst_listToVec _ isSemiformula_Pall (by rfl) _ hes (by row_entriesB)]
  all_goals try row_entries_simpB
  row_finish

/-! ### `congExs` — `“p' q' p q. …”`, `m = 4` -/

noncomputable def row_congExs_as : List V := [subst LAct (listToVec [bv 1, bv 3]) PeqB, subst LAct (listToVec [bv 0, bv 2]) PeqB, subst LAct (listToVec [bv 3, bv 2]) Pexs]
noncomputable def row_congExs_c : V := subst LAct (listToVec [bv 1, bv 0]) Pexs

theorem quote_row_congExs : (⌜Semiformula.lMap emb congExsB⌝ : V) = impChain LAct row_congExs_as row_congExs_c := by
  unfold congExsB row_congExs_as row_congExs_c PeqB Pexs
  all_goals row_shapeB

lemma isSemiformula_congExs_c : IsSemiformula LAct ((4 : ℕ) : V) row_congExs_c := by
  unfold row_congExs_c
  exact isSemiformula_substRow isSemiformula_Pexs _ (by rfl) (by row_entriesB)

/-- `congExs` at the witnesses `[wq, wp, wqp, wpp]` (the DSL variables right-to-left). -/
lemma inst_congExs {wq wp wqp wpp : V} (hwq : IsSemiterm LAct 0 wq) (hwp : IsSemiterm LAct 0 wp) (hwqp : IsSemiterm LAct 0 wqp) (hwpp : IsSemiterm LAct 0 wpp) :
    row_congExs_as.map (instOuter LAct [wq, wp, wqp, wpp]) = [eqFactB wqp wq, eqFactB wpp wp, exsFact wq wp] ∧
    instOuter LAct [wq, wp, wqp, wpp] row_congExs_c = exsFact wqp wpp := by
  have hes : ∀ e ∈ ([wq, wp, wqp, wpp] : List V), IsSemiterm LAct 0 e := (List.forall_mem_cons.mpr ⟨hwq, List.forall_mem_cons.mpr ⟨hwp, List.forall_mem_cons.mpr ⟨hwqp, List.forall_mem_cons.mpr ⟨hwpp, List.forall_mem_nil _⟩⟩⟩⟩)
  unfold row_congExs_as row_congExs_c
  simp only [List.map_cons, List.map_nil]
  rw [instOuter_subst_listToVec _ isSemiformula_PeqB (by rfl) _ hes (by row_entriesB), instOuter_subst_listToVec _ isSemiformula_PeqB (by rfl) _ hes (by row_entriesB), instOuter_subst_listToVec _ isSemiformula_Pexs (by rfl) _ hes (by row_entriesB), instOuter_subst_listToVec _ isSemiformula_Pexs (by rfl) _ hes (by row_entriesB)]
  all_goals try row_entries_simpB
  row_finish

/-! ### `congRel` — `“v' r' v R k r. …”`, `m = 6` -/

noncomputable def row_congRel_as : List V := [subst LAct (listToVec [bv 1, bv 5]) PeqB, subst LAct (listToVec [bv 0, bv 2]) PeqB, subst LAct (listToVec [bv 5, bv 4, bv 3, bv 2]) Prel]
noncomputable def row_congRel_c : V := subst LAct (listToVec [bv 1, bv 4, bv 3, bv 0]) Prel

theorem quote_row_congRel : (⌜Semiformula.lMap emb congRelB⌝ : V) = impChain LAct row_congRel_as row_congRel_c := by
  unfold congRelB row_congRel_as row_congRel_c PeqB Prel
  all_goals row_shapeB

lemma isSemiformula_congRel_c : IsSemiformula LAct ((6 : ℕ) : V) row_congRel_c := by
  unfold row_congRel_c
  exact isSemiformula_substRow isSemiformula_Prel _ (by rfl) (by row_entriesB)

/-- `congRel` at the witnesses `[wr, wk, wR, wv, wrp, wvp]` (the DSL variables right-to-left). -/
lemma inst_congRel {wr wk wR wv wrp wvp : V} (hwr : IsSemiterm LAct 0 wr) (hwk : IsSemiterm LAct 0 wk) (hwR : IsSemiterm LAct 0 wR) (hwv : IsSemiterm LAct 0 wv) (hwrp : IsSemiterm LAct 0 wrp) (hwvp : IsSemiterm LAct 0 wvp) :
    row_congRel_as.map (instOuter LAct [wr, wk, wR, wv, wrp, wvp]) = [eqFactB wrp wr, eqFactB wvp wv, relFact wr wk wR wv] ∧
    instOuter LAct [wr, wk, wR, wv, wrp, wvp] row_congRel_c = relFact wrp wk wR wvp := by
  have hes : ∀ e ∈ ([wr, wk, wR, wv, wrp, wvp] : List V), IsSemiterm LAct 0 e := (List.forall_mem_cons.mpr ⟨hwr, List.forall_mem_cons.mpr ⟨hwk, List.forall_mem_cons.mpr ⟨hwR, List.forall_mem_cons.mpr ⟨hwv, List.forall_mem_cons.mpr ⟨hwrp, List.forall_mem_cons.mpr ⟨hwvp, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩)
  unfold row_congRel_as row_congRel_c
  simp only [List.map_cons, List.map_nil]
  rw [instOuter_subst_listToVec _ isSemiformula_PeqB (by rfl) _ hes (by row_entriesB), instOuter_subst_listToVec _ isSemiformula_PeqB (by rfl) _ hes (by row_entriesB), instOuter_subst_listToVec _ isSemiformula_Prel (by rfl) _ hes (by row_entriesB), instOuter_subst_listToVec _ isSemiformula_Prel (by rfl) _ hes (by row_entriesB)]
  all_goals try row_entries_simpB
  row_finish

/-! ### `congNRel` — `“v' r' v R k r. …”`, `m = 6` -/

noncomputable def row_congNRel_as : List V := [subst LAct (listToVec [bv 1, bv 5]) PeqB, subst LAct (listToVec [bv 0, bv 2]) PeqB, subst LAct (listToVec [bv 5, bv 4, bv 3, bv 2]) Pnrel]
noncomputable def row_congNRel_c : V := subst LAct (listToVec [bv 1, bv 4, bv 3, bv 0]) Pnrel

theorem quote_row_congNRel : (⌜Semiformula.lMap emb congNRelB⌝ : V) = impChain LAct row_congNRel_as row_congNRel_c := by
  unfold congNRelB row_congNRel_as row_congNRel_c PeqB Pnrel
  all_goals row_shapeB

lemma isSemiformula_congNRel_c : IsSemiformula LAct ((6 : ℕ) : V) row_congNRel_c := by
  unfold row_congNRel_c
  exact isSemiformula_substRow isSemiformula_Pnrel _ (by rfl) (by row_entriesB)

/-- `congNRel` at the witnesses `[wr, wk, wR, wv, wrp, wvp]` (the DSL variables right-to-left). -/
lemma inst_congNRel {wr wk wR wv wrp wvp : V} (hwr : IsSemiterm LAct 0 wr) (hwk : IsSemiterm LAct 0 wk) (hwR : IsSemiterm LAct 0 wR) (hwv : IsSemiterm LAct 0 wv) (hwrp : IsSemiterm LAct 0 wrp) (hwvp : IsSemiterm LAct 0 wvp) :
    row_congNRel_as.map (instOuter LAct [wr, wk, wR, wv, wrp, wvp]) = [eqFactB wrp wr, eqFactB wvp wv, nrelFact wr wk wR wv] ∧
    instOuter LAct [wr, wk, wR, wv, wrp, wvp] row_congNRel_c = nrelFact wrp wk wR wvp := by
  have hes : ∀ e ∈ ([wr, wk, wR, wv, wrp, wvp] : List V), IsSemiterm LAct 0 e := (List.forall_mem_cons.mpr ⟨hwr, List.forall_mem_cons.mpr ⟨hwk, List.forall_mem_cons.mpr ⟨hwR, List.forall_mem_cons.mpr ⟨hwv, List.forall_mem_cons.mpr ⟨hwrp, List.forall_mem_cons.mpr ⟨hwvp, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩)
  unfold row_congNRel_as row_congNRel_c
  simp only [List.map_cons, List.map_nil]
  rw [instOuter_subst_listToVec _ isSemiformula_PeqB (by rfl) _ hes (by row_entriesB), instOuter_subst_listToVec _ isSemiformula_PeqB (by rfl) _ hes (by row_entriesB), instOuter_subst_listToVec _ isSemiformula_Pnrel (by rfl) _ hes (by row_entriesB), instOuter_subst_listToVec _ isSemiformula_Pnrel (by rfl) _ hes (by row_entriesB)]
  all_goals try row_entries_simpB
  row_finish

/-! ### `congVerum` — `“p' p. …”`, `m = 2` -/

noncomputable def row_congVerum_as : List V := [subst LAct (listToVec [bv 0, bv 1]) PeqB, subst LAct (listToVec [bv 1]) Pverum]
noncomputable def row_congVerum_c : V := subst LAct (listToVec [bv 0]) Pverum

theorem quote_row_congVerum : (⌜Semiformula.lMap emb congVerumB⌝ : V) = impChain LAct row_congVerum_as row_congVerum_c := by
  unfold congVerumB row_congVerum_as row_congVerum_c PeqB Pverum
  all_goals row_shapeB

lemma isSemiformula_congVerum_c : IsSemiformula LAct ((2 : ℕ) : V) row_congVerum_c := by
  unfold row_congVerum_c
  exact isSemiformula_substRow isSemiformula_Pverum _ (by rfl) (by row_entriesB)

/-- `congVerum` at the witnesses `[wp, wpp]` (the DSL variables right-to-left). -/
lemma inst_congVerum {wp wpp : V} (hwp : IsSemiterm LAct 0 wp) (hwpp : IsSemiterm LAct 0 wpp) :
    row_congVerum_as.map (instOuter LAct [wp, wpp]) = [eqFactB wpp wp, verumFact wp] ∧
    instOuter LAct [wp, wpp] row_congVerum_c = verumFact wpp := by
  have hes : ∀ e ∈ ([wp, wpp] : List V), IsSemiterm LAct 0 e := (List.forall_mem_cons.mpr ⟨hwp, List.forall_mem_cons.mpr ⟨hwpp, List.forall_mem_nil _⟩⟩)
  unfold row_congVerum_as row_congVerum_c
  simp only [List.map_cons, List.map_nil]
  rw [instOuter_subst_listToVec _ isSemiformula_PeqB (by rfl) _ hes (by row_entriesB), instOuter_subst_listToVec _ isSemiformula_Pverum (by rfl) _ hes (by row_entriesB), instOuter_subst_listToVec _ isSemiformula_Pverum (by rfl) _ hes (by row_entriesB)]
  all_goals try row_entries_simpB
  row_finish

/-! ### `congFalsum` — `“p' p. …”`, `m = 2` -/

noncomputable def row_congFalsum_as : List V := [subst LAct (listToVec [bv 0, bv 1]) PeqB, subst LAct (listToVec [bv 1]) Pfalsum]
noncomputable def row_congFalsum_c : V := subst LAct (listToVec [bv 0]) Pfalsum

theorem quote_row_congFalsum : (⌜Semiformula.lMap emb congFalsumB⌝ : V) = impChain LAct row_congFalsum_as row_congFalsum_c := by
  unfold congFalsumB row_congFalsum_as row_congFalsum_c PeqB Pfalsum
  all_goals row_shapeB

lemma isSemiformula_congFalsum_c : IsSemiformula LAct ((2 : ℕ) : V) row_congFalsum_c := by
  unfold row_congFalsum_c
  exact isSemiformula_substRow isSemiformula_Pfalsum _ (by rfl) (by row_entriesB)

/-- `congFalsum` at the witnesses `[wp, wpp]` (the DSL variables right-to-left). -/
lemma inst_congFalsum {wp wpp : V} (hwp : IsSemiterm LAct 0 wp) (hwpp : IsSemiterm LAct 0 wpp) :
    row_congFalsum_as.map (instOuter LAct [wp, wpp]) = [eqFactB wpp wp, falsumFact wp] ∧
    instOuter LAct [wp, wpp] row_congFalsum_c = falsumFact wpp := by
  have hes : ∀ e ∈ ([wp, wpp] : List V), IsSemiterm LAct 0 e := (List.forall_mem_cons.mpr ⟨hwp, List.forall_mem_cons.mpr ⟨hwpp, List.forall_mem_nil _⟩⟩)
  unfold row_congFalsum_as row_congFalsum_c
  simp only [List.map_cons, List.map_nil]
  rw [instOuter_subst_listToVec _ isSemiformula_PeqB (by rfl) _ hes (by row_entriesB), instOuter_subst_listToVec _ isSemiformula_Pfalsum (by rfl) _ hes (by row_entriesB), instOuter_subst_listToVec _ isSemiformula_Pfalsum (by rfl) _ hes (by row_entriesB)]
  all_goals try row_entries_simpB
  row_finish

/-! ### `congFunc` — `“v' t' v f k t. …”`, `m = 6` -/

noncomputable def row_congFunc_as : List V := [subst LAct (listToVec [bv 1, bv 5]) PeqB, subst LAct (listToVec [bv 0, bv 2]) PeqB, subst LAct (listToVec [bv 5, bv 4, bv 3, bv 2]) Pfunc]
noncomputable def row_congFunc_c : V := subst LAct (listToVec [bv 1, bv 4, bv 3, bv 0]) Pfunc

theorem quote_row_congFunc : (⌜Semiformula.lMap emb congFuncB⌝ : V) = impChain LAct row_congFunc_as row_congFunc_c := by
  unfold congFuncB row_congFunc_as row_congFunc_c PeqB Pfunc
  all_goals row_shapeB

lemma isSemiformula_congFunc_c : IsSemiformula LAct ((6 : ℕ) : V) row_congFunc_c := by
  unfold row_congFunc_c
  exact isSemiformula_substRow isSemiformula_Pfunc _ (by rfl) (by row_entriesB)

/-- `congFunc` at the witnesses `[wt, wk, wf, wv, wtp, wvp]` (the DSL variables right-to-left). -/
lemma inst_congFunc {wt wk wf wv wtp wvp : V} (hwt : IsSemiterm LAct 0 wt) (hwk : IsSemiterm LAct 0 wk) (hwf : IsSemiterm LAct 0 wf) (hwv : IsSemiterm LAct 0 wv) (hwtp : IsSemiterm LAct 0 wtp) (hwvp : IsSemiterm LAct 0 wvp) :
    row_congFunc_as.map (instOuter LAct [wt, wk, wf, wv, wtp, wvp]) = [eqFactB wtp wt, eqFactB wvp wv, funcFact wt wk wf wv] ∧
    instOuter LAct [wt, wk, wf, wv, wtp, wvp] row_congFunc_c = funcFact wtp wk wf wvp := by
  have hes : ∀ e ∈ ([wt, wk, wf, wv, wtp, wvp] : List V), IsSemiterm LAct 0 e := (List.forall_mem_cons.mpr ⟨hwt, List.forall_mem_cons.mpr ⟨hwk, List.forall_mem_cons.mpr ⟨hwf, List.forall_mem_cons.mpr ⟨hwv, List.forall_mem_cons.mpr ⟨hwtp, List.forall_mem_cons.mpr ⟨hwvp, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩)
  unfold row_congFunc_as row_congFunc_c
  simp only [List.map_cons, List.map_nil]
  rw [instOuter_subst_listToVec _ isSemiformula_PeqB (by rfl) _ hes (by row_entriesB), instOuter_subst_listToVec _ isSemiformula_PeqB (by rfl) _ hes (by row_entriesB), instOuter_subst_listToVec _ isSemiformula_Pfunc (by rfl) _ hes (by row_entriesB), instOuter_subst_listToVec _ isSemiformula_Pfunc (by rfl) _ hes (by row_entriesB)]
  all_goals try row_entries_simpB
  row_finish

/-! ### `congBvar` — `“t' t z. …”`, `m = 3` -/

noncomputable def row_congBvar_as : List V := [subst LAct (listToVec [bv 0, bv 1]) PeqB, subst LAct (listToVec [bv 1, bv 2]) Pbvar]
noncomputable def row_congBvar_c : V := subst LAct (listToVec [bv 0, bv 2]) Pbvar

theorem quote_row_congBvar : (⌜Semiformula.lMap emb congBvarB⌝ : V) = impChain LAct row_congBvar_as row_congBvar_c := by
  unfold congBvarB row_congBvar_as row_congBvar_c Pbvar PeqB
  all_goals row_shapeB

lemma isSemiformula_congBvar_c : IsSemiformula LAct ((3 : ℕ) : V) row_congBvar_c := by
  unfold row_congBvar_c
  exact isSemiformula_substRow isSemiformula_Pbvar _ (by rfl) (by row_entriesB)

/-- `congBvar` at the witnesses `[wz, wt, wtp]` (the DSL variables right-to-left). -/
lemma inst_congBvar {wz wt wtp : V} (hwz : IsSemiterm LAct 0 wz) (hwt : IsSemiterm LAct 0 wt) (hwtp : IsSemiterm LAct 0 wtp) :
    row_congBvar_as.map (instOuter LAct [wz, wt, wtp]) = [eqFactB wtp wt, bvarFact wt wz] ∧
    instOuter LAct [wz, wt, wtp] row_congBvar_c = bvarFact wtp wz := by
  have hes : ∀ e ∈ ([wz, wt, wtp] : List V), IsSemiterm LAct 0 e := (List.forall_mem_cons.mpr ⟨hwz, List.forall_mem_cons.mpr ⟨hwt, List.forall_mem_cons.mpr ⟨hwtp, List.forall_mem_nil _⟩⟩⟩)
  unfold row_congBvar_as row_congBvar_c
  simp only [List.map_cons, List.map_nil]
  rw [instOuter_subst_listToVec _ isSemiformula_PeqB (by rfl) _ hes (by row_entriesB), instOuter_subst_listToVec _ isSemiformula_Pbvar (by rfl) _ hes (by row_entriesB), instOuter_subst_listToVec _ isSemiformula_Pbvar (by rfl) _ hes (by row_entriesB)]
  all_goals try row_entries_simpB
  row_finish

/-! ### `congFvar` — `“t' t x. …”`, `m = 3` -/

noncomputable def row_congFvar_as : List V := [subst LAct (listToVec [bv 0, bv 1]) PeqB, subst LAct (listToVec [bv 1, bv 2]) Pfvar]
noncomputable def row_congFvar_c : V := subst LAct (listToVec [bv 0, bv 2]) Pfvar

theorem quote_row_congFvar : (⌜Semiformula.lMap emb congFvarB⌝ : V) = impChain LAct row_congFvar_as row_congFvar_c := by
  unfold congFvarB row_congFvar_as row_congFvar_c PeqB Pfvar
  all_goals row_shapeB

lemma isSemiformula_congFvar_c : IsSemiformula LAct ((3 : ℕ) : V) row_congFvar_c := by
  unfold row_congFvar_c
  exact isSemiformula_substRow isSemiformula_Pfvar _ (by rfl) (by row_entriesB)

/-- `congFvar` at the witnesses `[wx, wt, wtp]` (the DSL variables right-to-left). -/
lemma inst_congFvar {wx wt wtp : V} (hwx : IsSemiterm LAct 0 wx) (hwt : IsSemiterm LAct 0 wt) (hwtp : IsSemiterm LAct 0 wtp) :
    row_congFvar_as.map (instOuter LAct [wx, wt, wtp]) = [eqFactB wtp wt, fvarFact wt wx] ∧
    instOuter LAct [wx, wt, wtp] row_congFvar_c = fvarFact wtp wx := by
  have hes : ∀ e ∈ ([wx, wt, wtp] : List V), IsSemiterm LAct 0 e := (List.forall_mem_cons.mpr ⟨hwx, List.forall_mem_cons.mpr ⟨hwt, List.forall_mem_cons.mpr ⟨hwtp, List.forall_mem_nil _⟩⟩⟩)
  unfold row_congFvar_as row_congFvar_c
  simp only [List.map_cons, List.map_nil]
  rw [instOuter_subst_listToVec _ isSemiformula_PeqB (by rfl) _ hes (by row_entriesB), instOuter_subst_listToVec _ isSemiformula_Pfvar (by rfl) _ hes (by row_entriesB), instOuter_subst_listToVec _ isSemiformula_Pfvar (by rfl) _ hes (by row_entriesB)]
  all_goals try row_entries_simpB
  row_finish

/-! ### `congAdj` — `“w' v' t' w v t. …”`, `m = 6` -/

noncomputable def row_congAdj_as : List V := [subst LAct (listToVec [bv 0, bv 3]) PeqB, subst LAct (listToVec [bv 2, bv 5]) PeqB, subst LAct (listToVec [bv 1, bv 4]) PeqB, subst LAct (listToVec [bv 3, bv 5, bv 4]) Padjoin]
noncomputable def row_congAdj_c : V := subst LAct (listToVec [bv 0, bv 2, bv 1]) Padjoin

theorem quote_row_congAdj : (⌜Semiformula.lMap emb congAdjB⌝ : V) = impChain LAct row_congAdj_as row_congAdj_c := by
  unfold congAdjB row_congAdj_as row_congAdj_c Padjoin PeqB
  all_goals row_shapeB

lemma isSemiformula_congAdj_c : IsSemiformula LAct ((6 : ℕ) : V) row_congAdj_c := by
  unfold row_congAdj_c
  exact isSemiformula_substRow isSemiformula_Padjoin _ (by rfl) (by row_entriesB)

/-- `congAdj` at the witnesses `[wt, wv, ww, wtp, wvp, wwp]` (the DSL variables right-to-left). -/
lemma inst_congAdj {wt wv ww wtp wvp wwp : V} (hwt : IsSemiterm LAct 0 wt) (hwv : IsSemiterm LAct 0 wv) (hww : IsSemiterm LAct 0 ww) (hwtp : IsSemiterm LAct 0 wtp) (hwvp : IsSemiterm LAct 0 wvp) (hwwp : IsSemiterm LAct 0 wwp) :
    row_congAdj_as.map (instOuter LAct [wt, wv, ww, wtp, wvp, wwp]) = [eqFactB wwp ww, eqFactB wtp wt, eqFactB wvp wv, adjFact ww wt wv] ∧
    instOuter LAct [wt, wv, ww, wtp, wvp, wwp] row_congAdj_c = adjFact wwp wtp wvp := by
  have hes : ∀ e ∈ ([wt, wv, ww, wtp, wvp, wwp] : List V), IsSemiterm LAct 0 e := (List.forall_mem_cons.mpr ⟨hwt, List.forall_mem_cons.mpr ⟨hwv, List.forall_mem_cons.mpr ⟨hww, List.forall_mem_cons.mpr ⟨hwtp, List.forall_mem_cons.mpr ⟨hwvp, List.forall_mem_cons.mpr ⟨hwwp, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩)
  unfold row_congAdj_as row_congAdj_c
  simp only [List.map_cons, List.map_nil]
  rw [instOuter_subst_listToVec _ isSemiformula_PeqB (by rfl) _ hes (by row_entriesB), instOuter_subst_listToVec _ isSemiformula_PeqB (by rfl) _ hes (by row_entriesB), instOuter_subst_listToVec _ isSemiformula_PeqB (by rfl) _ hes (by row_entriesB), instOuter_subst_listToVec _ isSemiformula_Padjoin (by rfl) _ hes (by row_entriesB), instOuter_subst_listToVec _ isSemiformula_Padjoin (by rfl) _ hes (by row_entriesB)]
  all_goals try row_entries_simpB
  row_finish

/-! ### `congLen` — `“y x l. …”`, `m = 3` -/

noncomputable def row_congLen_as : List V := [subst LAct (listToVec [bv 0, bv 1]) PeqB, subst LAct (listToVec [bv 2, bv 1]) PflenG]
noncomputable def row_congLen_c : V := subst LAct (listToVec [bv 2, bv 0]) PflenG

theorem quote_row_congLen : (⌜Semiformula.lMap emb congLenB⌝ : V) = impChain LAct row_congLen_as row_congLen_c := by
  unfold congLenB row_congLen_as row_congLen_c PeqB PflenG
  all_goals row_shapeB

lemma isSemiformula_congLen_c : IsSemiformula LAct ((3 : ℕ) : V) row_congLen_c := by
  unfold row_congLen_c
  exact isSemiformula_substRow isSemiformula_PflenG _ (by rfl) (by row_entriesB)

/-- `congLen` at the witnesses `[wl, wx, wy]` (the DSL variables right-to-left). -/
lemma inst_congLen {wl wx wy : V} (hwl : IsSemiterm LAct 0 wl) (hwx : IsSemiterm LAct 0 wx) (hwy : IsSemiterm LAct 0 wy) :
    row_congLen_as.map (instOuter LAct [wl, wx, wy]) = [eqFactB wy wx, lenFact wl wx] ∧
    instOuter LAct [wl, wx, wy] row_congLen_c = lenFact wl wy := by
  have hes : ∀ e ∈ ([wl, wx, wy] : List V), IsSemiterm LAct 0 e := (List.forall_mem_cons.mpr ⟨hwl, List.forall_mem_cons.mpr ⟨hwx, List.forall_mem_cons.mpr ⟨hwy, List.forall_mem_nil _⟩⟩⟩)
  unfold row_congLen_as row_congLen_c
  simp only [List.map_cons, List.map_nil]
  rw [instOuter_subst_listToVec _ isSemiformula_PeqB (by rfl) _ hes (by row_entriesB), instOuter_subst_listToVec _ isSemiformula_PflenG (by rfl) _ hes (by row_entriesB), instOuter_subst_listToVec _ isSemiformula_PflenG (by rfl) _ hes (by row_entriesB)]
  all_goals try row_entries_simpB
  row_finish

/-! ### `congTLen` — `“y x l. …”`, `m = 3` -/

noncomputable def row_congTLen_as : List V := [subst LAct (listToVec [bv 0, bv 1]) PeqB, subst LAct (listToVec [bv 2, bv 1]) PtlenG]
noncomputable def row_congTLen_c : V := subst LAct (listToVec [bv 2, bv 0]) PtlenG

theorem quote_row_congTLen : (⌜Semiformula.lMap emb congTLenB⌝ : V) = impChain LAct row_congTLen_as row_congTLen_c := by
  unfold congTLenB row_congTLen_as row_congTLen_c PeqB PtlenG
  all_goals row_shapeB

lemma isSemiformula_congTLen_c : IsSemiformula LAct ((3 : ℕ) : V) row_congTLen_c := by
  unfold row_congTLen_c
  exact isSemiformula_substRow isSemiformula_PtlenG _ (by rfl) (by row_entriesB)

/-- `congTLen` at the witnesses `[wl, wx, wy]` (the DSL variables right-to-left). -/
lemma inst_congTLen {wl wx wy : V} (hwl : IsSemiterm LAct 0 wl) (hwx : IsSemiterm LAct 0 wx) (hwy : IsSemiterm LAct 0 wy) :
    row_congTLen_as.map (instOuter LAct [wl, wx, wy]) = [eqFactB wy wx, termLenMetaFact wl wx] ∧
    instOuter LAct [wl, wx, wy] row_congTLen_c = termLenMetaFact wl wy := by
  have hes : ∀ e ∈ ([wl, wx, wy] : List V), IsSemiterm LAct 0 e := (List.forall_mem_cons.mpr ⟨hwl, List.forall_mem_cons.mpr ⟨hwx, List.forall_mem_cons.mpr ⟨hwy, List.forall_mem_nil _⟩⟩⟩)
  unfold row_congTLen_as row_congTLen_c
  simp only [List.map_cons, List.map_nil]
  rw [instOuter_subst_listToVec _ isSemiformula_PeqB (by rfl) _ hes (by row_entriesB), instOuter_subst_listToVec _ isSemiformula_PtlenG (by rfl) _ hes (by row_entriesB), instOuter_subst_listToVec _ isSemiformula_PtlenG (by rfl) _ hes (by row_entriesB)]
  all_goals try row_entries_simpB
  row_finish

/-! ### `congLenNum` — `“l' l y. …”`, `m = 3` -/

noncomputable def row_congLenNum_as : List V := [subst LAct (listToVec [bv 1, bv 0]) PeqB, subst LAct (listToVec [bv 1, bv 2]) PflenG]
noncomputable def row_congLenNum_c : V := subst LAct (listToVec [bv 0, bv 2]) PflenG

theorem quote_row_congLenNum : (⌜Semiformula.lMap emb congLenNumB⌝ : V) = impChain LAct row_congLenNum_as row_congLenNum_c := by
  unfold congLenNumB row_congLenNum_as row_congLenNum_c PeqB PflenG
  all_goals row_shapeB

lemma isSemiformula_congLenNum_c : IsSemiformula LAct ((3 : ℕ) : V) row_congLenNum_c := by
  unfold row_congLenNum_c
  exact isSemiformula_substRow isSemiformula_PflenG _ (by rfl) (by row_entriesB)

/-- `congLenNum` at the witnesses `[wy, wl, wlp]` (the DSL variables right-to-left). -/
lemma inst_congLenNum {wy wl wlp : V} (hwy : IsSemiterm LAct 0 wy) (hwl : IsSemiterm LAct 0 wl) (hwlp : IsSemiterm LAct 0 wlp) :
    row_congLenNum_as.map (instOuter LAct [wy, wl, wlp]) = [eqFactB wl wlp, lenFact wl wy] ∧
    instOuter LAct [wy, wl, wlp] row_congLenNum_c = lenFact wlp wy := by
  have hes : ∀ e ∈ ([wy, wl, wlp] : List V), IsSemiterm LAct 0 e := (List.forall_mem_cons.mpr ⟨hwy, List.forall_mem_cons.mpr ⟨hwl, List.forall_mem_cons.mpr ⟨hwlp, List.forall_mem_nil _⟩⟩⟩)
  unfold row_congLenNum_as row_congLenNum_c
  simp only [List.map_cons, List.map_nil]
  rw [instOuter_subst_listToVec _ isSemiformula_PeqB (by rfl) _ hes (by row_entriesB), instOuter_subst_listToVec _ isSemiformula_PflenG (by rfl) _ hes (by row_entriesB), instOuter_subst_listToVec _ isSemiformula_PflenG (by rfl) _ hes (by row_entriesB)]
  all_goals try row_entries_simpB
  row_finish

/-! ### `congTLenNum` — `“l' l t. …”`, `m = 3` -/

noncomputable def row_congTLenNum_as : List V := [subst LAct (listToVec [bv 1, bv 0]) PeqB, subst LAct (listToVec [bv 1, bv 2]) PtlenG]
noncomputable def row_congTLenNum_c : V := subst LAct (listToVec [bv 0, bv 2]) PtlenG

theorem quote_row_congTLenNum : (⌜Semiformula.lMap emb congTLenNumB⌝ : V) = impChain LAct row_congTLenNum_as row_congTLenNum_c := by
  unfold congTLenNumB row_congTLenNum_as row_congTLenNum_c PeqB PtlenG
  all_goals row_shapeB

lemma isSemiformula_congTLenNum_c : IsSemiformula LAct ((3 : ℕ) : V) row_congTLenNum_c := by
  unfold row_congTLenNum_c
  exact isSemiformula_substRow isSemiformula_PtlenG _ (by rfl) (by row_entriesB)

/-- `congTLenNum` at the witnesses `[wt, wl, wlp]` (the DSL variables right-to-left). -/
lemma inst_congTLenNum {wt wl wlp : V} (hwt : IsSemiterm LAct 0 wt) (hwl : IsSemiterm LAct 0 wl) (hwlp : IsSemiterm LAct 0 wlp) :
    row_congTLenNum_as.map (instOuter LAct [wt, wl, wlp]) = [eqFactB wl wlp, termLenMetaFact wl wt] ∧
    instOuter LAct [wt, wl, wlp] row_congTLenNum_c = termLenMetaFact wlp wt := by
  have hes : ∀ e ∈ ([wt, wl, wlp] : List V), IsSemiterm LAct 0 e := (List.forall_mem_cons.mpr ⟨hwt, List.forall_mem_cons.mpr ⟨hwl, List.forall_mem_cons.mpr ⟨hwlp, List.forall_mem_nil _⟩⟩⟩)
  unfold row_congTLenNum_as row_congTLenNum_c
  simp only [List.map_cons, List.map_nil]
  rw [instOuter_subst_listToVec _ isSemiformula_PeqB (by rfl) _ hes (by row_entriesB), instOuter_subst_listToVec _ isSemiformula_PtlenG (by rfl) _ hes (by row_entriesB), instOuter_subst_listToVec _ isSemiformula_PtlenG (by rfl) _ hes (by row_entriesB)]
  all_goals try row_entries_simpB
  row_finish

/-! ### `congMem` — `“s y x. …”`, `m = 3` -/

noncomputable def row_congMem_as : List V := [subst LAct (listToVec [bv 1, bv 2]) PeqB, subst LAct (listToVec [bv 2, bv 0]) Pmem]
noncomputable def row_congMem_c : V := subst LAct (listToVec [bv 1, bv 0]) Pmem

theorem quote_row_congMem : (⌜Semiformula.lMap emb congMemB⌝ : V) = impChain LAct row_congMem_as row_congMem_c := by
  unfold congMemB row_congMem_as row_congMem_c PeqB Pmem
  all_goals row_shapeB

lemma isSemiformula_congMem_c : IsSemiformula LAct ((3 : ℕ) : V) row_congMem_c := by
  unfold row_congMem_c
  exact isSemiformula_substRow isSemiformula_Pmem _ (by rfl) (by row_entriesB)

/-- `congMem` at the witnesses `[wx, wy, ws]` (the DSL variables right-to-left). -/
lemma inst_congMem {wx wy ws : V} (hwx : IsSemiterm LAct 0 wx) (hwy : IsSemiterm LAct 0 wy) (hws : IsSemiterm LAct 0 ws) :
    row_congMem_as.map (instOuter LAct [wx, wy, ws]) = [eqFactB wy wx, memFact wx ws] ∧
    instOuter LAct [wx, wy, ws] row_congMem_c = memFact wy ws := by
  have hes : ∀ e ∈ ([wx, wy, ws] : List V), IsSemiterm LAct 0 e := (List.forall_mem_cons.mpr ⟨hwx, List.forall_mem_cons.mpr ⟨hwy, List.forall_mem_cons.mpr ⟨hws, List.forall_mem_nil _⟩⟩⟩)
  unfold row_congMem_as row_congMem_c
  simp only [List.map_cons, List.map_nil]
  rw [instOuter_subst_listToVec _ isSemiformula_PeqB (by rfl) _ hes (by row_entriesB), instOuter_subst_listToVec _ isSemiformula_Pmem (by rfl) _ hes (by row_entriesB), instOuter_subst_listToVec _ isSemiformula_Pmem (by rfl) _ hes (by row_entriesB)]
  all_goals try row_entries_simpB
  row_finish

/-! ### `congMemSet` — `“s' s x. …”`, `m = 3` -/

noncomputable def row_congMemSet_as : List V := [subst LAct (listToVec [bv 0, bv 1]) PeqB, subst LAct (listToVec [bv 2, bv 1]) Pmem]
noncomputable def row_congMemSet_c : V := subst LAct (listToVec [bv 2, bv 0]) Pmem

/-! ### `congFstIdx` — `“t' t d. …”`, `m = 3` -/

noncomputable def row_congFstIdx_as : List V := [subst LAct (listToVec [bv 0, bv 1]) PeqB, subst LAct (listToVec [bv 1, bv 2]) PfstIdx]
noncomputable def row_congFstIdx_c : V := subst LAct (listToVec [bv 0, bv 2]) PfstIdx

theorem quote_row_congFstIdx : (⌜Semiformula.lMap emb congFstIdxB⌝ : V) = impChain LAct row_congFstIdx_as row_congFstIdx_c := by
  unfold congFstIdxB row_congFstIdx_as row_congFstIdx_c PeqB PfstIdx fstIdxS
  all_goals row_shapeB

lemma isSemiformula_congFstIdx_c : IsSemiformula LAct ((3 : ℕ) : V) row_congFstIdx_c := by
  unfold row_congFstIdx_c
  exact isSemiformula_substRow isSemiformula_PfstIdx _ (by rfl) (by row_entriesB)

/-- `congFstIdx` at the witnesses `[wd, wt, wtp]` (the DSL variables right-to-left). -/
lemma inst_congFstIdx {wd wt wtp : V} (hwd : IsSemiterm LAct 0 wd) (hwt : IsSemiterm LAct 0 wt) (hwtp : IsSemiterm LAct 0 wtp) :
    row_congFstIdx_as.map (instOuter LAct [wd, wt, wtp]) = [eqFactB wtp wt, fstIdxFact wt wd] ∧
    instOuter LAct [wd, wt, wtp] row_congFstIdx_c = fstIdxFact wtp wd := by
  have hes : ∀ e ∈ ([wd, wt, wtp] : List V), IsSemiterm LAct 0 e := (List.forall_mem_cons.mpr ⟨hwd, List.forall_mem_cons.mpr ⟨hwt, List.forall_mem_cons.mpr ⟨hwtp, List.forall_mem_nil _⟩⟩⟩)
  unfold row_congFstIdx_as row_congFstIdx_c
  simp only [List.map_cons, List.map_nil]
  rw [instOuter_subst_listToVec _ isSemiformula_PeqB (by rfl) _ hes (by row_entriesB), instOuter_subst_listToVec _ isSemiformula_PfstIdx (by rfl) _ hes (by row_entriesB), instOuter_subst_listToVec _ isSemiformula_PfstIdx (by rfl) _ hes (by row_entriesB)]
  all_goals try row_entries_simpB
  row_finish

/-! ### `congSubsetL` — `“u t' t. …”`, `m = 3` -/

noncomputable def row_congSubsetL_as : List V := [subst LAct (listToVec [bv 1, bv 2]) PeqB, subst LAct (listToVec [bv 2, bv 0]) Psubset]
noncomputable def row_congSubsetL_c : V := subst LAct (listToVec [bv 1, bv 0]) Psubset

theorem quote_row_congSubsetL : (⌜Semiformula.lMap emb congSubsetLB⌝ : V) = impChain LAct row_congSubsetL_as row_congSubsetL_c := by
  unfold congSubsetLB row_congSubsetL_as row_congSubsetL_c PeqB Psubset
  all_goals row_shapeB

lemma isSemiformula_congSubsetL_c : IsSemiformula LAct ((3 : ℕ) : V) row_congSubsetL_c := by
  unfold row_congSubsetL_c
  exact isSemiformula_substRow isSemiformula_Psubset _ (by rfl) (by row_entriesB)

/-- `congSubsetL` at the witnesses `[wt, wtp, wu]` (the DSL variables right-to-left). -/
lemma inst_congSubsetL {wt wtp wu : V} (hwt : IsSemiterm LAct 0 wt) (hwtp : IsSemiterm LAct 0 wtp) (hwu : IsSemiterm LAct 0 wu) :
    row_congSubsetL_as.map (instOuter LAct [wt, wtp, wu]) = [eqFactB wtp wt, subsetFact wt wu] ∧
    instOuter LAct [wt, wtp, wu] row_congSubsetL_c = subsetFact wtp wu := by
  have hes : ∀ e ∈ ([wt, wtp, wu] : List V), IsSemiterm LAct 0 e := (List.forall_mem_cons.mpr ⟨hwt, List.forall_mem_cons.mpr ⟨hwtp, List.forall_mem_cons.mpr ⟨hwu, List.forall_mem_nil _⟩⟩⟩)
  unfold row_congSubsetL_as row_congSubsetL_c
  simp only [List.map_cons, List.map_nil]
  rw [instOuter_subst_listToVec _ isSemiformula_PeqB (by rfl) _ hes (by row_entriesB), instOuter_subst_listToVec _ isSemiformula_Psubset (by rfl) _ hes (by row_entriesB), instOuter_subst_listToVec _ isSemiformula_Psubset (by rfl) _ hes (by row_entriesB)]
  all_goals try row_entries_simpB
  row_finish

/-! ### `congSetShiftL` — `“s t' t. …”`, `m = 3` -/

noncomputable def row_congSetShiftL_as : List V := [subst LAct (listToVec [bv 1, bv 2]) PeqB, subst LAct (listToVec [bv 2, bv 0]) PsetShiftG]
noncomputable def row_congSetShiftL_c : V := subst LAct (listToVec [bv 1, bv 0]) PsetShiftG

theorem quote_row_congSetShiftL : (⌜Semiformula.lMap emb congSetShiftLB⌝ : V) = impChain LAct row_congSetShiftL_as row_congSetShiftL_c := by
  unfold congSetShiftLB row_congSetShiftL_as row_congSetShiftL_c PeqB PsetShiftG
  all_goals row_shapeB

lemma isSemiformula_congSetShiftL_c : IsSemiformula LAct ((3 : ℕ) : V) row_congSetShiftL_c := by
  unfold row_congSetShiftL_c
  exact isSemiformula_substRow isSemiformula_PsetShiftG _ (by rfl) (by row_entriesB)

/-- `congSetShiftL` at the witnesses `[wt, wtp, ws]` (the DSL variables right-to-left). -/
lemma inst_congSetShiftL {wt wtp ws : V} (hwt : IsSemiterm LAct 0 wt) (hwtp : IsSemiterm LAct 0 wtp) (hws : IsSemiterm LAct 0 ws) :
    row_congSetShiftL_as.map (instOuter LAct [wt, wtp, ws]) = [eqFactB wtp wt, setShiftFact wt ws] ∧
    instOuter LAct [wt, wtp, ws] row_congSetShiftL_c = setShiftFact wtp ws := by
  have hes : ∀ e ∈ ([wt, wtp, ws] : List V), IsSemiterm LAct 0 e := (List.forall_mem_cons.mpr ⟨hwt, List.forall_mem_cons.mpr ⟨hwtp, List.forall_mem_cons.mpr ⟨hws, List.forall_mem_nil _⟩⟩⟩)
  unfold row_congSetShiftL_as row_congSetShiftL_c
  simp only [List.map_cons, List.map_nil]
  rw [instOuter_subst_listToVec _ isSemiformula_PeqB (by rfl) _ hes (by row_entriesB), instOuter_subst_listToVec _ isSemiformula_PsetShiftG (by rfl) _ hes (by row_entriesB), instOuter_subst_listToVec _ isSemiformula_PsetShiftG (by rfl) _ hes (by row_entriesB)]
  all_goals try row_entries_simpB
  row_finish

/-! ### `congSetShiftR` — `“s' s t. …”`, `m = 3` -/

noncomputable def row_congSetShiftR_as : List V := [subst LAct (listToVec [bv 0, bv 1]) PeqB, subst LAct (listToVec [bv 2, bv 1]) PsetShiftG]
noncomputable def row_congSetShiftR_c : V := subst LAct (listToVec [bv 2, bv 0]) PsetShiftG

theorem quote_row_congSetShiftR : (⌜Semiformula.lMap emb congSetShiftRB⌝ : V) = impChain LAct row_congSetShiftR_as row_congSetShiftR_c := by
  unfold congSetShiftRB row_congSetShiftR_as row_congSetShiftR_c PeqB PsetShiftG
  all_goals row_shapeB

lemma isSemiformula_congSetShiftR_c : IsSemiformula LAct ((3 : ℕ) : V) row_congSetShiftR_c := by
  unfold row_congSetShiftR_c
  exact isSemiformula_substRow isSemiformula_PsetShiftG _ (by rfl) (by row_entriesB)

/-- `congSetShiftR` at the witnesses `[wt, ws, wsp]` (the DSL variables right-to-left). -/
lemma inst_congSetShiftR {wt ws wsp : V} (hwt : IsSemiterm LAct 0 wt) (hws : IsSemiterm LAct 0 ws) (hwsp : IsSemiterm LAct 0 wsp) :
    row_congSetShiftR_as.map (instOuter LAct [wt, ws, wsp]) = [eqFactB wsp ws, setShiftFact wt ws] ∧
    instOuter LAct [wt, ws, wsp] row_congSetShiftR_c = setShiftFact wt wsp := by
  have hes : ∀ e ∈ ([wt, ws, wsp] : List V), IsSemiterm LAct 0 e := (List.forall_mem_cons.mpr ⟨hwt, List.forall_mem_cons.mpr ⟨hws, List.forall_mem_cons.mpr ⟨hwsp, List.forall_mem_nil _⟩⟩⟩)
  unfold row_congSetShiftR_as row_congSetShiftR_c
  simp only [List.map_cons, List.map_nil]
  rw [instOuter_subst_listToVec _ isSemiformula_PeqB (by rfl) _ hes (by row_entriesB), instOuter_subst_listToVec _ isSemiformula_PsetShiftG (by rfl) _ hes (by row_entriesB), instOuter_subst_listToVec _ isSemiformula_PsetShiftG (by rfl) _ hes (by row_entriesB)]
  all_goals try row_entries_simpB
  row_finish

/-! ### `congShiftL` — `“x y' y. …”`, `m = 3` -/

noncomputable def row_congShiftL_as : List V := [subst LAct (listToVec [bv 1, bv 2]) PeqB, subst LAct (listToVec [bv 2, bv 0]) PshiftG]
noncomputable def row_congShiftL_c : V := subst LAct (listToVec [bv 1, bv 0]) PshiftG

/-! ### `congSubstArg` — `“n' n w y. …”`, `m = 4` -/

noncomputable def row_congSubstArg_as : List V := [subst LAct (listToVec [bv 1, bv 0]) PeqB, subst LAct (listToVec [bv 3, bv 2, bv 1]) PsubstsG]
noncomputable def row_congSubstArg_c : V := subst LAct (listToVec [bv 3, bv 2, bv 0]) PsubstsG

theorem quote_row_congSubstArg : (⌜Semiformula.lMap emb congSubstArgB⌝ : V) = impChain LAct row_congSubstArg_as row_congSubstArg_c := by
  unfold congSubstArgB row_congSubstArg_as row_congSubstArg_c PeqB PsubstsG
  all_goals row_shapeB

lemma isSemiformula_congSubstArg_c : IsSemiformula LAct ((4 : ℕ) : V) row_congSubstArg_c := by
  unfold row_congSubstArg_c
  exact isSemiformula_substRow isSemiformula_PsubstsG _ (by rfl) (by row_entriesB)

/-- `congSubstArg` at the witnesses `[wy, ww, wn, wnp]` (the DSL variables right-to-left). -/
lemma inst_congSubstArg {wy ww wn wnp : V} (hwy : IsSemiterm LAct 0 wy) (hww : IsSemiterm LAct 0 ww) (hwn : IsSemiterm LAct 0 wn) (hwnp : IsSemiterm LAct 0 wnp) :
    row_congSubstArg_as.map (instOuter LAct [wy, ww, wn, wnp]) = [eqFactB wn wnp, substFact wy ww wn] ∧
    instOuter LAct [wy, ww, wn, wnp] row_congSubstArg_c = substFact wy ww wnp := by
  have hes : ∀ e ∈ ([wy, ww, wn, wnp] : List V), IsSemiterm LAct 0 e := (List.forall_mem_cons.mpr ⟨hwy, List.forall_mem_cons.mpr ⟨hww, List.forall_mem_cons.mpr ⟨hwn, List.forall_mem_cons.mpr ⟨hwnp, List.forall_mem_nil _⟩⟩⟩⟩)
  unfold row_congSubstArg_as row_congSubstArg_c
  simp only [List.map_cons, List.map_nil]
  rw [instOuter_subst_listToVec _ isSemiformula_PeqB (by rfl) _ hes (by row_entriesB), instOuter_subst_listToVec _ isSemiformula_PsubstsG (by rfl) _ hes (by row_entriesB), instOuter_subst_listToVec _ isSemiformula_PsubstsG (by rfl) _ hes (by row_entriesB)]
  all_goals try row_entries_simpB
  row_finish

/-! ### `congInsertS` — `“s' s x t. …”`, `m = 4` -/

noncomputable def row_congInsertS_as : List V := [subst LAct (listToVec [bv 0, bv 1]) PeqB, subst LAct (listToVec [bv 3, bv 2, bv 1]) Pinsert]
noncomputable def row_congInsertS_c : V := subst LAct (listToVec [bv 3, bv 2, bv 0]) Pinsert

theorem quote_row_congInsertS : (⌜Semiformula.lMap emb congInsertSB⌝ : V) = impChain LAct row_congInsertS_as row_congInsertS_c := by
  unfold congInsertSB row_congInsertS_as row_congInsertS_c PeqB Pinsert
  all_goals row_shapeB

lemma isSemiformula_congInsertS_c : IsSemiformula LAct ((4 : ℕ) : V) row_congInsertS_c := by
  unfold row_congInsertS_c
  exact isSemiformula_substRow isSemiformula_Pinsert _ (by rfl) (by row_entriesB)

/-- `congInsertS` at the witnesses `[wt, wx, ws, wsp]` (the DSL variables right-to-left). -/
lemma inst_congInsertS {wt wx ws wsp : V} (hwt : IsSemiterm LAct 0 wt) (hwx : IsSemiterm LAct 0 wx) (hws : IsSemiterm LAct 0 ws) (hwsp : IsSemiterm LAct 0 wsp) :
    row_congInsertS_as.map (instOuter LAct [wt, wx, ws, wsp]) = [eqFactB wsp ws, insFact wt wx ws] ∧
    instOuter LAct [wt, wx, ws, wsp] row_congInsertS_c = insFact wt wx wsp := by
  have hes : ∀ e ∈ ([wt, wx, ws, wsp] : List V), IsSemiterm LAct 0 e := (List.forall_mem_cons.mpr ⟨hwt, List.forall_mem_cons.mpr ⟨hwx, List.forall_mem_cons.mpr ⟨hws, List.forall_mem_cons.mpr ⟨hwsp, List.forall_mem_nil _⟩⟩⟩⟩)
  unfold row_congInsertS_as row_congInsertS_c
  simp only [List.map_cons, List.map_nil]
  rw [instOuter_subst_listToVec _ isSemiformula_PeqB (by rfl) _ hes (by row_entriesB), instOuter_subst_listToVec _ isSemiformula_Pinsert (by rfl) _ hes (by row_entriesB), instOuter_subst_listToVec _ isSemiformula_Pinsert (by rfl) _ hes (by row_entriesB)]
  all_goals try row_entries_simpB
  row_finish

/-! ### `congSetLenR` — `“l s' s. …”`, `m = 3` -/

noncomputable def row_congSetLenR_as : List V := [subst LAct (listToVec [bv 1, bv 2]) PeqB, subst LAct (listToVec [bv 0, bv 2]) PsetLen]
noncomputable def row_congSetLenR_c : V := subst LAct (listToVec [bv 0, bv 1]) PsetLen

theorem quote_row_congSetLenR : (⌜Semiformula.lMap emb congSetLenRB⌝ : V) = impChain LAct row_congSetLenR_as row_congSetLenR_c := by
  unfold congSetLenRB row_congSetLenR_as row_congSetLenR_c PeqB PsetLen
  all_goals row_shapeB

lemma isSemiformula_congSetLenR_c : IsSemiformula LAct ((3 : ℕ) : V) row_congSetLenR_c := by
  unfold row_congSetLenR_c
  exact isSemiformula_substRow isSemiformula_PsetLen _ (by rfl) (by row_entriesB)

/-- `congSetLenR` at the witnesses `[ws, wsp, wl]` (the DSL variables right-to-left). -/
lemma inst_congSetLenR {ws wsp wl : V} (hws : IsSemiterm LAct 0 ws) (hwsp : IsSemiterm LAct 0 wsp) (hwl : IsSemiterm LAct 0 wl) :
    row_congSetLenR_as.map (instOuter LAct [ws, wsp, wl]) = [eqFactB wsp ws, sequentLenFact wl ws] ∧
    instOuter LAct [ws, wsp, wl] row_congSetLenR_c = sequentLenFact wl wsp := by
  have hes : ∀ e ∈ ([ws, wsp, wl] : List V), IsSemiterm LAct 0 e := (List.forall_mem_cons.mpr ⟨hws, List.forall_mem_cons.mpr ⟨hwsp, List.forall_mem_cons.mpr ⟨hwl, List.forall_mem_nil _⟩⟩⟩)
  unfold row_congSetLenR_as row_congSetLenR_c
  simp only [List.map_cons, List.map_nil]
  rw [instOuter_subst_listToVec _ isSemiformula_PeqB (by rfl) _ hes (by row_entriesB), instOuter_subst_listToVec _ isSemiformula_PsetLen (by rfl) _ hes (by row_entriesB), instOuter_subst_listToVec _ isSemiformula_PsetLen (by rfl) _ hes (by row_entriesB)]
  all_goals try row_entries_simpB
  row_finish

/-! ## B. Identification: the injectivity rows (§3.5) -/

/-! ### `eqOfAnd` — `“y q' p' q p x. …”`, `m = 6` -/

noncomputable def row_eqOfAnd_as : List V := [subst LAct (listToVec [bv 5, bv 4, bv 3]) Pand, subst LAct (listToVec [bv 0, bv 2, bv 1]) Pand, subst LAct (listToVec [bv 4, bv 2]) PeqB, subst LAct (listToVec [bv 3, bv 1]) PeqB]
noncomputable def row_eqOfAnd_c : V := subst LAct (listToVec [bv 5, bv 0]) PeqB

theorem quote_row_eqOfAnd : (⌜Semiformula.lMap emb eqOfAndB⌝ : V) = impChain LAct row_eqOfAnd_as row_eqOfAnd_c := by
  unfold eqOfAndB row_eqOfAnd_as row_eqOfAnd_c Pand PeqB
  all_goals row_shapeB

lemma isSemiformula_eqOfAnd_c : IsSemiformula LAct ((6 : ℕ) : V) row_eqOfAnd_c := by
  unfold row_eqOfAnd_c
  exact isSemiformula_substRow isSemiformula_PeqB _ (by rfl) (by row_entriesB)

/-- `eqOfAnd` at the witnesses `[wx, wp, wq, wpp, wqp, wy]` (the DSL variables right-to-left). -/
lemma inst_eqOfAnd {wx wp wq wpp wqp wy : V} (hwx : IsSemiterm LAct 0 wx) (hwp : IsSemiterm LAct 0 wp) (hwq : IsSemiterm LAct 0 wq) (hwpp : IsSemiterm LAct 0 wpp) (hwqp : IsSemiterm LAct 0 wqp) (hwy : IsSemiterm LAct 0 wy) :
    row_eqOfAnd_as.map (instOuter LAct [wx, wp, wq, wpp, wqp, wy]) = [andFact wx wp wq, andFact wy wpp wqp, eqFactB wp wpp, eqFactB wq wqp] ∧
    instOuter LAct [wx, wp, wq, wpp, wqp, wy] row_eqOfAnd_c = eqFactB wx wy := by
  have hes : ∀ e ∈ ([wx, wp, wq, wpp, wqp, wy] : List V), IsSemiterm LAct 0 e := (List.forall_mem_cons.mpr ⟨hwx, List.forall_mem_cons.mpr ⟨hwp, List.forall_mem_cons.mpr ⟨hwq, List.forall_mem_cons.mpr ⟨hwpp, List.forall_mem_cons.mpr ⟨hwqp, List.forall_mem_cons.mpr ⟨hwy, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩)
  unfold row_eqOfAnd_as row_eqOfAnd_c
  simp only [List.map_cons, List.map_nil]
  rw [instOuter_subst_listToVec _ isSemiformula_Pand (by rfl) _ hes (by row_entriesB), instOuter_subst_listToVec _ isSemiformula_Pand (by rfl) _ hes (by row_entriesB), instOuter_subst_listToVec _ isSemiformula_PeqB (by rfl) _ hes (by row_entriesB), instOuter_subst_listToVec _ isSemiformula_PeqB (by rfl) _ hes (by row_entriesB), instOuter_subst_listToVec _ isSemiformula_PeqB (by rfl) _ hes (by row_entriesB)]
  all_goals try row_entries_simpB
  row_finish

/-! ### `eqOfOr` — `“y q' p' q p x. …”`, `m = 6` -/

noncomputable def row_eqOfOr_as : List V := [subst LAct (listToVec [bv 5, bv 4, bv 3]) Por, subst LAct (listToVec [bv 0, bv 2, bv 1]) Por, subst LAct (listToVec [bv 4, bv 2]) PeqB, subst LAct (listToVec [bv 3, bv 1]) PeqB]
noncomputable def row_eqOfOr_c : V := subst LAct (listToVec [bv 5, bv 0]) PeqB

theorem quote_row_eqOfOr : (⌜Semiformula.lMap emb eqOfOrB⌝ : V) = impChain LAct row_eqOfOr_as row_eqOfOr_c := by
  unfold eqOfOrB row_eqOfOr_as row_eqOfOr_c PeqB Por
  all_goals row_shapeB

lemma isSemiformula_eqOfOr_c : IsSemiformula LAct ((6 : ℕ) : V) row_eqOfOr_c := by
  unfold row_eqOfOr_c
  exact isSemiformula_substRow isSemiformula_PeqB _ (by rfl) (by row_entriesB)

/-- `eqOfOr` at the witnesses `[wx, wp, wq, wpp, wqp, wy]` (the DSL variables right-to-left). -/
lemma inst_eqOfOr {wx wp wq wpp wqp wy : V} (hwx : IsSemiterm LAct 0 wx) (hwp : IsSemiterm LAct 0 wp) (hwq : IsSemiterm LAct 0 wq) (hwpp : IsSemiterm LAct 0 wpp) (hwqp : IsSemiterm LAct 0 wqp) (hwy : IsSemiterm LAct 0 wy) :
    row_eqOfOr_as.map (instOuter LAct [wx, wp, wq, wpp, wqp, wy]) = [orFact wx wp wq, orFact wy wpp wqp, eqFactB wp wpp, eqFactB wq wqp] ∧
    instOuter LAct [wx, wp, wq, wpp, wqp, wy] row_eqOfOr_c = eqFactB wx wy := by
  have hes : ∀ e ∈ ([wx, wp, wq, wpp, wqp, wy] : List V), IsSemiterm LAct 0 e := (List.forall_mem_cons.mpr ⟨hwx, List.forall_mem_cons.mpr ⟨hwp, List.forall_mem_cons.mpr ⟨hwq, List.forall_mem_cons.mpr ⟨hwpp, List.forall_mem_cons.mpr ⟨hwqp, List.forall_mem_cons.mpr ⟨hwy, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩)
  unfold row_eqOfOr_as row_eqOfOr_c
  simp only [List.map_cons, List.map_nil]
  rw [instOuter_subst_listToVec _ isSemiformula_Por (by rfl) _ hes (by row_entriesB), instOuter_subst_listToVec _ isSemiformula_Por (by rfl) _ hes (by row_entriesB), instOuter_subst_listToVec _ isSemiformula_PeqB (by rfl) _ hes (by row_entriesB), instOuter_subst_listToVec _ isSemiformula_PeqB (by rfl) _ hes (by row_entriesB), instOuter_subst_listToVec _ isSemiformula_PeqB (by rfl) _ hes (by row_entriesB)]
  all_goals try row_entries_simpB
  row_finish

/-! ### `eqOfAll` — `“y p' p x. …”`, `m = 4` -/

noncomputable def row_eqOfAll_as : List V := [subst LAct (listToVec [bv 3, bv 2]) Pall, subst LAct (listToVec [bv 0, bv 1]) Pall, subst LAct (listToVec [bv 2, bv 1]) PeqB]
noncomputable def row_eqOfAll_c : V := subst LAct (listToVec [bv 3, bv 0]) PeqB

theorem quote_row_eqOfAll : (⌜Semiformula.lMap emb eqOfAllB⌝ : V) = impChain LAct row_eqOfAll_as row_eqOfAll_c := by
  unfold eqOfAllB row_eqOfAll_as row_eqOfAll_c Pall PeqB
  all_goals row_shapeB

lemma isSemiformula_eqOfAll_c : IsSemiformula LAct ((4 : ℕ) : V) row_eqOfAll_c := by
  unfold row_eqOfAll_c
  exact isSemiformula_substRow isSemiformula_PeqB _ (by rfl) (by row_entriesB)

/-- `eqOfAll` at the witnesses `[wx, wp, wpp, wy]` (the DSL variables right-to-left). -/
lemma inst_eqOfAll {wx wp wpp wy : V} (hwx : IsSemiterm LAct 0 wx) (hwp : IsSemiterm LAct 0 wp) (hwpp : IsSemiterm LAct 0 wpp) (hwy : IsSemiterm LAct 0 wy) :
    row_eqOfAll_as.map (instOuter LAct [wx, wp, wpp, wy]) = [allFact wx wp, allFact wy wpp, eqFactB wp wpp] ∧
    instOuter LAct [wx, wp, wpp, wy] row_eqOfAll_c = eqFactB wx wy := by
  have hes : ∀ e ∈ ([wx, wp, wpp, wy] : List V), IsSemiterm LAct 0 e := (List.forall_mem_cons.mpr ⟨hwx, List.forall_mem_cons.mpr ⟨hwp, List.forall_mem_cons.mpr ⟨hwpp, List.forall_mem_cons.mpr ⟨hwy, List.forall_mem_nil _⟩⟩⟩⟩)
  unfold row_eqOfAll_as row_eqOfAll_c
  simp only [List.map_cons, List.map_nil]
  rw [instOuter_subst_listToVec _ isSemiformula_Pall (by rfl) _ hes (by row_entriesB), instOuter_subst_listToVec _ isSemiformula_Pall (by rfl) _ hes (by row_entriesB), instOuter_subst_listToVec _ isSemiformula_PeqB (by rfl) _ hes (by row_entriesB), instOuter_subst_listToVec _ isSemiformula_PeqB (by rfl) _ hes (by row_entriesB)]
  all_goals try row_entries_simpB
  row_finish

/-! ### `eqOfExs` — `“y p' p x. …”`, `m = 4` -/

noncomputable def row_eqOfExs_as : List V := [subst LAct (listToVec [bv 3, bv 2]) Pexs, subst LAct (listToVec [bv 0, bv 1]) Pexs, subst LAct (listToVec [bv 2, bv 1]) PeqB]
noncomputable def row_eqOfExs_c : V := subst LAct (listToVec [bv 3, bv 0]) PeqB

theorem quote_row_eqOfExs : (⌜Semiformula.lMap emb eqOfExsB⌝ : V) = impChain LAct row_eqOfExs_as row_eqOfExs_c := by
  unfold eqOfExsB row_eqOfExs_as row_eqOfExs_c PeqB Pexs
  all_goals row_shapeB

lemma isSemiformula_eqOfExs_c : IsSemiformula LAct ((4 : ℕ) : V) row_eqOfExs_c := by
  unfold row_eqOfExs_c
  exact isSemiformula_substRow isSemiformula_PeqB _ (by rfl) (by row_entriesB)

/-- `eqOfExs` at the witnesses `[wx, wp, wpp, wy]` (the DSL variables right-to-left). -/
lemma inst_eqOfExs {wx wp wpp wy : V} (hwx : IsSemiterm LAct 0 wx) (hwp : IsSemiterm LAct 0 wp) (hwpp : IsSemiterm LAct 0 wpp) (hwy : IsSemiterm LAct 0 wy) :
    row_eqOfExs_as.map (instOuter LAct [wx, wp, wpp, wy]) = [exsFact wx wp, exsFact wy wpp, eqFactB wp wpp] ∧
    instOuter LAct [wx, wp, wpp, wy] row_eqOfExs_c = eqFactB wx wy := by
  have hes : ∀ e ∈ ([wx, wp, wpp, wy] : List V), IsSemiterm LAct 0 e := (List.forall_mem_cons.mpr ⟨hwx, List.forall_mem_cons.mpr ⟨hwp, List.forall_mem_cons.mpr ⟨hwpp, List.forall_mem_cons.mpr ⟨hwy, List.forall_mem_nil _⟩⟩⟩⟩)
  unfold row_eqOfExs_as row_eqOfExs_c
  simp only [List.map_cons, List.map_nil]
  rw [instOuter_subst_listToVec _ isSemiformula_Pexs (by rfl) _ hes (by row_entriesB), instOuter_subst_listToVec _ isSemiformula_Pexs (by rfl) _ hes (by row_entriesB), instOuter_subst_listToVec _ isSemiformula_PeqB (by rfl) _ hes (by row_entriesB), instOuter_subst_listToVec _ isSemiformula_PeqB (by rfl) _ hes (by row_entriesB)]
  all_goals try row_entries_simpB
  row_finish

/-! ### `eqOfRel` — `“y v' v R k x. …”`, `m = 6` -/

noncomputable def row_eqOfRel_as : List V := [subst LAct (listToVec [bv 5, bv 4, bv 3, bv 2]) Prel, subst LAct (listToVec [bv 0, bv 4, bv 3, bv 1]) Prel, subst LAct (listToVec [bv 2, bv 1]) PeqB]
noncomputable def row_eqOfRel_c : V := subst LAct (listToVec [bv 5, bv 0]) PeqB

theorem quote_row_eqOfRel : (⌜Semiformula.lMap emb eqOfRelB⌝ : V) = impChain LAct row_eqOfRel_as row_eqOfRel_c := by
  unfold eqOfRelB row_eqOfRel_as row_eqOfRel_c PeqB Prel
  all_goals row_shapeB

lemma isSemiformula_eqOfRel_c : IsSemiformula LAct ((6 : ℕ) : V) row_eqOfRel_c := by
  unfold row_eqOfRel_c
  exact isSemiformula_substRow isSemiformula_PeqB _ (by rfl) (by row_entriesB)

/-- `eqOfRel` at the witnesses `[wx, wk, wR, wv, wvp, wy]` (the DSL variables right-to-left). -/
lemma inst_eqOfRel {wx wk wR wv wvp wy : V} (hwx : IsSemiterm LAct 0 wx) (hwk : IsSemiterm LAct 0 wk) (hwR : IsSemiterm LAct 0 wR) (hwv : IsSemiterm LAct 0 wv) (hwvp : IsSemiterm LAct 0 wvp) (hwy : IsSemiterm LAct 0 wy) :
    row_eqOfRel_as.map (instOuter LAct [wx, wk, wR, wv, wvp, wy]) = [relFact wx wk wR wv, relFact wy wk wR wvp, eqFactB wv wvp] ∧
    instOuter LAct [wx, wk, wR, wv, wvp, wy] row_eqOfRel_c = eqFactB wx wy := by
  have hes : ∀ e ∈ ([wx, wk, wR, wv, wvp, wy] : List V), IsSemiterm LAct 0 e := (List.forall_mem_cons.mpr ⟨hwx, List.forall_mem_cons.mpr ⟨hwk, List.forall_mem_cons.mpr ⟨hwR, List.forall_mem_cons.mpr ⟨hwv, List.forall_mem_cons.mpr ⟨hwvp, List.forall_mem_cons.mpr ⟨hwy, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩)
  unfold row_eqOfRel_as row_eqOfRel_c
  simp only [List.map_cons, List.map_nil]
  rw [instOuter_subst_listToVec _ isSemiformula_Prel (by rfl) _ hes (by row_entriesB), instOuter_subst_listToVec _ isSemiformula_Prel (by rfl) _ hes (by row_entriesB), instOuter_subst_listToVec _ isSemiformula_PeqB (by rfl) _ hes (by row_entriesB), instOuter_subst_listToVec _ isSemiformula_PeqB (by rfl) _ hes (by row_entriesB)]
  all_goals try row_entries_simpB
  row_finish

/-! ### `eqOfNRel` — `“y v' v R k x. …”`, `m = 6` -/

noncomputable def row_eqOfNRel_as : List V := [subst LAct (listToVec [bv 5, bv 4, bv 3, bv 2]) Pnrel, subst LAct (listToVec [bv 0, bv 4, bv 3, bv 1]) Pnrel, subst LAct (listToVec [bv 2, bv 1]) PeqB]
noncomputable def row_eqOfNRel_c : V := subst LAct (listToVec [bv 5, bv 0]) PeqB

theorem quote_row_eqOfNRel : (⌜Semiformula.lMap emb eqOfNRelB⌝ : V) = impChain LAct row_eqOfNRel_as row_eqOfNRel_c := by
  unfold eqOfNRelB row_eqOfNRel_as row_eqOfNRel_c PeqB Pnrel
  all_goals row_shapeB

lemma isSemiformula_eqOfNRel_c : IsSemiformula LAct ((6 : ℕ) : V) row_eqOfNRel_c := by
  unfold row_eqOfNRel_c
  exact isSemiformula_substRow isSemiformula_PeqB _ (by rfl) (by row_entriesB)

/-- `eqOfNRel` at the witnesses `[wx, wk, wR, wv, wvp, wy]` (the DSL variables right-to-left). -/
lemma inst_eqOfNRel {wx wk wR wv wvp wy : V} (hwx : IsSemiterm LAct 0 wx) (hwk : IsSemiterm LAct 0 wk) (hwR : IsSemiterm LAct 0 wR) (hwv : IsSemiterm LAct 0 wv) (hwvp : IsSemiterm LAct 0 wvp) (hwy : IsSemiterm LAct 0 wy) :
    row_eqOfNRel_as.map (instOuter LAct [wx, wk, wR, wv, wvp, wy]) = [nrelFact wx wk wR wv, nrelFact wy wk wR wvp, eqFactB wv wvp] ∧
    instOuter LAct [wx, wk, wR, wv, wvp, wy] row_eqOfNRel_c = eqFactB wx wy := by
  have hes : ∀ e ∈ ([wx, wk, wR, wv, wvp, wy] : List V), IsSemiterm LAct 0 e := (List.forall_mem_cons.mpr ⟨hwx, List.forall_mem_cons.mpr ⟨hwk, List.forall_mem_cons.mpr ⟨hwR, List.forall_mem_cons.mpr ⟨hwv, List.forall_mem_cons.mpr ⟨hwvp, List.forall_mem_cons.mpr ⟨hwy, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩)
  unfold row_eqOfNRel_as row_eqOfNRel_c
  simp only [List.map_cons, List.map_nil]
  rw [instOuter_subst_listToVec _ isSemiformula_Pnrel (by rfl) _ hes (by row_entriesB), instOuter_subst_listToVec _ isSemiformula_Pnrel (by rfl) _ hes (by row_entriesB), instOuter_subst_listToVec _ isSemiformula_PeqB (by rfl) _ hes (by row_entriesB), instOuter_subst_listToVec _ isSemiformula_PeqB (by rfl) _ hes (by row_entriesB)]
  all_goals try row_entries_simpB
  row_finish

/-! ### `eqOfVerum` — `“y x. …”`, `m = 2` -/

noncomputable def row_eqOfVerum_as : List V := [subst LAct (listToVec [bv 1]) Pverum, subst LAct (listToVec [bv 0]) Pverum]
noncomputable def row_eqOfVerum_c : V := subst LAct (listToVec [bv 1, bv 0]) PeqB

theorem quote_row_eqOfVerum : (⌜Semiformula.lMap emb eqOfVerumB⌝ : V) = impChain LAct row_eqOfVerum_as row_eqOfVerum_c := by
  unfold eqOfVerumB row_eqOfVerum_as row_eqOfVerum_c PeqB Pverum
  all_goals row_shapeB

lemma isSemiformula_eqOfVerum_c : IsSemiformula LAct ((2 : ℕ) : V) row_eqOfVerum_c := by
  unfold row_eqOfVerum_c
  exact isSemiformula_substRow isSemiformula_PeqB _ (by rfl) (by row_entriesB)

/-- `eqOfVerum` at the witnesses `[wx, wy]` (the DSL variables right-to-left). -/
lemma inst_eqOfVerum {wx wy : V} (hwx : IsSemiterm LAct 0 wx) (hwy : IsSemiterm LAct 0 wy) :
    row_eqOfVerum_as.map (instOuter LAct [wx, wy]) = [verumFact wx, verumFact wy] ∧
    instOuter LAct [wx, wy] row_eqOfVerum_c = eqFactB wx wy := by
  have hes : ∀ e ∈ ([wx, wy] : List V), IsSemiterm LAct 0 e := (List.forall_mem_cons.mpr ⟨hwx, List.forall_mem_cons.mpr ⟨hwy, List.forall_mem_nil _⟩⟩)
  unfold row_eqOfVerum_as row_eqOfVerum_c
  simp only [List.map_cons, List.map_nil]
  rw [instOuter_subst_listToVec _ isSemiformula_Pverum (by rfl) _ hes (by row_entriesB), instOuter_subst_listToVec _ isSemiformula_Pverum (by rfl) _ hes (by row_entriesB), instOuter_subst_listToVec _ isSemiformula_PeqB (by rfl) _ hes (by row_entriesB)]
  all_goals try row_entries_simpB
  row_finish

/-! ### `eqOfFalsum` — `“y x. …”`, `m = 2` -/

noncomputable def row_eqOfFalsum_as : List V := [subst LAct (listToVec [bv 1]) Pfalsum, subst LAct (listToVec [bv 0]) Pfalsum]
noncomputable def row_eqOfFalsum_c : V := subst LAct (listToVec [bv 1, bv 0]) PeqB

theorem quote_row_eqOfFalsum : (⌜Semiformula.lMap emb eqOfFalsumB⌝ : V) = impChain LAct row_eqOfFalsum_as row_eqOfFalsum_c := by
  unfold eqOfFalsumB row_eqOfFalsum_as row_eqOfFalsum_c PeqB Pfalsum
  all_goals row_shapeB

lemma isSemiformula_eqOfFalsum_c : IsSemiformula LAct ((2 : ℕ) : V) row_eqOfFalsum_c := by
  unfold row_eqOfFalsum_c
  exact isSemiformula_substRow isSemiformula_PeqB _ (by rfl) (by row_entriesB)

/-- `eqOfFalsum` at the witnesses `[wx, wy]` (the DSL variables right-to-left). -/
lemma inst_eqOfFalsum {wx wy : V} (hwx : IsSemiterm LAct 0 wx) (hwy : IsSemiterm LAct 0 wy) :
    row_eqOfFalsum_as.map (instOuter LAct [wx, wy]) = [falsumFact wx, falsumFact wy] ∧
    instOuter LAct [wx, wy] row_eqOfFalsum_c = eqFactB wx wy := by
  have hes : ∀ e ∈ ([wx, wy] : List V), IsSemiterm LAct 0 e := (List.forall_mem_cons.mpr ⟨hwx, List.forall_mem_cons.mpr ⟨hwy, List.forall_mem_nil _⟩⟩)
  unfold row_eqOfFalsum_as row_eqOfFalsum_c
  simp only [List.map_cons, List.map_nil]
  rw [instOuter_subst_listToVec _ isSemiformula_Pfalsum (by rfl) _ hes (by row_entriesB), instOuter_subst_listToVec _ isSemiformula_Pfalsum (by rfl) _ hes (by row_entriesB), instOuter_subst_listToVec _ isSemiformula_PeqB (by rfl) _ hes (by row_entriesB)]
  all_goals try row_entries_simpB
  row_finish

/-! ### `eqOfFunc` — `“t' v' v f k t. …”`, `m = 6` -/

noncomputable def row_eqOfFunc_as : List V := [subst LAct (listToVec [bv 5, bv 4, bv 3, bv 2]) Pfunc, subst LAct (listToVec [bv 0, bv 4, bv 3, bv 1]) Pfunc, subst LAct (listToVec [bv 2, bv 1]) PeqB]
noncomputable def row_eqOfFunc_c : V := subst LAct (listToVec [bv 5, bv 0]) PeqB

theorem quote_row_eqOfFunc : (⌜Semiformula.lMap emb eqOfFuncB⌝ : V) = impChain LAct row_eqOfFunc_as row_eqOfFunc_c := by
  unfold eqOfFuncB row_eqOfFunc_as row_eqOfFunc_c PeqB Pfunc
  all_goals row_shapeB

lemma isSemiformula_eqOfFunc_c : IsSemiformula LAct ((6 : ℕ) : V) row_eqOfFunc_c := by
  unfold row_eqOfFunc_c
  exact isSemiformula_substRow isSemiformula_PeqB _ (by rfl) (by row_entriesB)

/-- `eqOfFunc` at the witnesses `[wt, wk, wf, wv, wvp, wtp]` (the DSL variables right-to-left). -/
lemma inst_eqOfFunc {wt wk wf wv wvp wtp : V} (hwt : IsSemiterm LAct 0 wt) (hwk : IsSemiterm LAct 0 wk) (hwf : IsSemiterm LAct 0 wf) (hwv : IsSemiterm LAct 0 wv) (hwvp : IsSemiterm LAct 0 wvp) (hwtp : IsSemiterm LAct 0 wtp) :
    row_eqOfFunc_as.map (instOuter LAct [wt, wk, wf, wv, wvp, wtp]) = [funcFact wt wk wf wv, funcFact wtp wk wf wvp, eqFactB wv wvp] ∧
    instOuter LAct [wt, wk, wf, wv, wvp, wtp] row_eqOfFunc_c = eqFactB wt wtp := by
  have hes : ∀ e ∈ ([wt, wk, wf, wv, wvp, wtp] : List V), IsSemiterm LAct 0 e := (List.forall_mem_cons.mpr ⟨hwt, List.forall_mem_cons.mpr ⟨hwk, List.forall_mem_cons.mpr ⟨hwf, List.forall_mem_cons.mpr ⟨hwv, List.forall_mem_cons.mpr ⟨hwvp, List.forall_mem_cons.mpr ⟨hwtp, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩)
  unfold row_eqOfFunc_as row_eqOfFunc_c
  simp only [List.map_cons, List.map_nil]
  rw [instOuter_subst_listToVec _ isSemiformula_Pfunc (by rfl) _ hes (by row_entriesB), instOuter_subst_listToVec _ isSemiformula_Pfunc (by rfl) _ hes (by row_entriesB), instOuter_subst_listToVec _ isSemiformula_PeqB (by rfl) _ hes (by row_entriesB), instOuter_subst_listToVec _ isSemiformula_PeqB (by rfl) _ hes (by row_entriesB)]
  all_goals try row_entries_simpB
  row_finish

/-! ### `eqOfBvar` — `“t' t z. …”`, `m = 3` -/

noncomputable def row_eqOfBvar_as : List V := [subst LAct (listToVec [bv 1, bv 2]) Pbvar, subst LAct (listToVec [bv 0, bv 2]) Pbvar]
noncomputable def row_eqOfBvar_c : V := subst LAct (listToVec [bv 1, bv 0]) PeqB

theorem quote_row_eqOfBvar : (⌜Semiformula.lMap emb eqOfBvarB⌝ : V) = impChain LAct row_eqOfBvar_as row_eqOfBvar_c := by
  unfold eqOfBvarB row_eqOfBvar_as row_eqOfBvar_c Pbvar PeqB
  all_goals row_shapeB

lemma isSemiformula_eqOfBvar_c : IsSemiformula LAct ((3 : ℕ) : V) row_eqOfBvar_c := by
  unfold row_eqOfBvar_c
  exact isSemiformula_substRow isSemiformula_PeqB _ (by rfl) (by row_entriesB)

/-- `eqOfBvar` at the witnesses `[wz, wt, wtp]` (the DSL variables right-to-left). -/
lemma inst_eqOfBvar {wz wt wtp : V} (hwz : IsSemiterm LAct 0 wz) (hwt : IsSemiterm LAct 0 wt) (hwtp : IsSemiterm LAct 0 wtp) :
    row_eqOfBvar_as.map (instOuter LAct [wz, wt, wtp]) = [bvarFact wt wz, bvarFact wtp wz] ∧
    instOuter LAct [wz, wt, wtp] row_eqOfBvar_c = eqFactB wt wtp := by
  have hes : ∀ e ∈ ([wz, wt, wtp] : List V), IsSemiterm LAct 0 e := (List.forall_mem_cons.mpr ⟨hwz, List.forall_mem_cons.mpr ⟨hwt, List.forall_mem_cons.mpr ⟨hwtp, List.forall_mem_nil _⟩⟩⟩)
  unfold row_eqOfBvar_as row_eqOfBvar_c
  simp only [List.map_cons, List.map_nil]
  rw [instOuter_subst_listToVec _ isSemiformula_Pbvar (by rfl) _ hes (by row_entriesB), instOuter_subst_listToVec _ isSemiformula_Pbvar (by rfl) _ hes (by row_entriesB), instOuter_subst_listToVec _ isSemiformula_PeqB (by rfl) _ hes (by row_entriesB)]
  all_goals try row_entries_simpB
  row_finish

/-! ### `eqOfFvar` — `“t' t x. …”`, `m = 3` -/

noncomputable def row_eqOfFvar_as : List V := [subst LAct (listToVec [bv 1, bv 2]) Pfvar, subst LAct (listToVec [bv 0, bv 2]) Pfvar]
noncomputable def row_eqOfFvar_c : V := subst LAct (listToVec [bv 1, bv 0]) PeqB

theorem quote_row_eqOfFvar : (⌜Semiformula.lMap emb eqOfFvarB⌝ : V) = impChain LAct row_eqOfFvar_as row_eqOfFvar_c := by
  unfold eqOfFvarB row_eqOfFvar_as row_eqOfFvar_c PeqB Pfvar
  all_goals row_shapeB

lemma isSemiformula_eqOfFvar_c : IsSemiformula LAct ((3 : ℕ) : V) row_eqOfFvar_c := by
  unfold row_eqOfFvar_c
  exact isSemiformula_substRow isSemiformula_PeqB _ (by rfl) (by row_entriesB)

/-- `eqOfFvar` at the witnesses `[wx, wt, wtp]` (the DSL variables right-to-left). -/
lemma inst_eqOfFvar {wx wt wtp : V} (hwx : IsSemiterm LAct 0 wx) (hwt : IsSemiterm LAct 0 wt) (hwtp : IsSemiterm LAct 0 wtp) :
    row_eqOfFvar_as.map (instOuter LAct [wx, wt, wtp]) = [fvarFact wt wx, fvarFact wtp wx] ∧
    instOuter LAct [wx, wt, wtp] row_eqOfFvar_c = eqFactB wt wtp := by
  have hes : ∀ e ∈ ([wx, wt, wtp] : List V), IsSemiterm LAct 0 e := (List.forall_mem_cons.mpr ⟨hwx, List.forall_mem_cons.mpr ⟨hwt, List.forall_mem_cons.mpr ⟨hwtp, List.forall_mem_nil _⟩⟩⟩)
  unfold row_eqOfFvar_as row_eqOfFvar_c
  simp only [List.map_cons, List.map_nil]
  rw [instOuter_subst_listToVec _ isSemiformula_Pfvar (by rfl) _ hes (by row_entriesB), instOuter_subst_listToVec _ isSemiformula_Pfvar (by rfl) _ hes (by row_entriesB), instOuter_subst_listToVec _ isSemiformula_PeqB (by rfl) _ hes (by row_entriesB)]
  all_goals try row_entries_simpB
  row_finish

/-! ### `eqOfAdj` — `“w' v' t' w v t. …”`, `m = 6` -/

noncomputable def row_eqOfAdj_as : List V := [subst LAct (listToVec [bv 3, bv 5, bv 4]) Padjoin, subst LAct (listToVec [bv 0, bv 2, bv 1]) Padjoin, subst LAct (listToVec [bv 5, bv 2]) PeqB, subst LAct (listToVec [bv 4, bv 1]) PeqB]
noncomputable def row_eqOfAdj_c : V := subst LAct (listToVec [bv 3, bv 0]) PeqB

theorem quote_row_eqOfAdj : (⌜Semiformula.lMap emb eqOfAdjB⌝ : V) = impChain LAct row_eqOfAdj_as row_eqOfAdj_c := by
  unfold eqOfAdjB row_eqOfAdj_as row_eqOfAdj_c Padjoin PeqB
  all_goals row_shapeB

lemma isSemiformula_eqOfAdj_c : IsSemiformula LAct ((6 : ℕ) : V) row_eqOfAdj_c := by
  unfold row_eqOfAdj_c
  exact isSemiformula_substRow isSemiformula_PeqB _ (by rfl) (by row_entriesB)

/-- `eqOfAdj` at the witnesses `[wt, wv, ww, wtp, wvp, wwp]` (the DSL variables right-to-left). -/
lemma inst_eqOfAdj {wt wv ww wtp wvp wwp : V} (hwt : IsSemiterm LAct 0 wt) (hwv : IsSemiterm LAct 0 wv) (hww : IsSemiterm LAct 0 ww) (hwtp : IsSemiterm LAct 0 wtp) (hwvp : IsSemiterm LAct 0 wvp) (hwwp : IsSemiterm LAct 0 wwp) :
    row_eqOfAdj_as.map (instOuter LAct [wt, wv, ww, wtp, wvp, wwp]) = [adjFact ww wt wv, adjFact wwp wtp wvp, eqFactB wt wtp, eqFactB wv wvp] ∧
    instOuter LAct [wt, wv, ww, wtp, wvp, wwp] row_eqOfAdj_c = eqFactB ww wwp := by
  have hes : ∀ e ∈ ([wt, wv, ww, wtp, wvp, wwp] : List V), IsSemiterm LAct 0 e := (List.forall_mem_cons.mpr ⟨hwt, List.forall_mem_cons.mpr ⟨hwv, List.forall_mem_cons.mpr ⟨hww, List.forall_mem_cons.mpr ⟨hwtp, List.forall_mem_cons.mpr ⟨hwvp, List.forall_mem_cons.mpr ⟨hwwp, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩)
  unfold row_eqOfAdj_as row_eqOfAdj_c
  simp only [List.map_cons, List.map_nil]
  rw [instOuter_subst_listToVec _ isSemiformula_Padjoin (by rfl) _ hes (by row_entriesB), instOuter_subst_listToVec _ isSemiformula_Padjoin (by rfl) _ hes (by row_entriesB), instOuter_subst_listToVec _ isSemiformula_PeqB (by rfl) _ hes (by row_entriesB), instOuter_subst_listToVec _ isSemiformula_PeqB (by rfl) _ hes (by row_entriesB), instOuter_subst_listToVec _ isSemiformula_PeqB (by rfl) _ hes (by row_entriesB)]
  all_goals try row_entries_simpB
  row_finish

/-! ## C. Functionality (`pinSteps`, §4.10(i)) -/

/-! ### `setShiftFun` — `“y' s y. …”`, `m = 3` -/

noncomputable def row_setShiftFun_as : List V := [subst LAct (listToVec [bv 2, bv 1]) PsetShiftG, subst LAct (listToVec [bv 0, bv 1]) PsetShiftG]
noncomputable def row_setShiftFun_c : V := subst LAct (listToVec [bv 2, bv 0]) PeqB

/-! ### `sequentLenFun` — `“y' s y. …”`, `m = 3` -/

noncomputable def row_sequentLenFun_as : List V := [subst LAct (listToVec [bv 2, bv 1]) PsetLen, subst LAct (listToVec [bv 0, bv 1]) PsetLen]
noncomputable def row_sequentLenFun_c : V := subst LAct (listToVec [bv 2, bv 0]) PeqB

/-- `sequentLenFun` at the witnesses `[wy, ws, wyp]` (the DSL variables right-to-left). -/
lemma inst_sequentLenFun {wy ws wyp : V} (hwy : IsSemiterm LAct 0 wy) (hws : IsSemiterm LAct 0 ws) (hwyp : IsSemiterm LAct 0 wyp) :
    row_sequentLenFun_as.map (instOuter LAct [wy, ws, wyp]) = [sequentLenFact wy ws, sequentLenFact wyp ws] ∧
    instOuter LAct [wy, ws, wyp] row_sequentLenFun_c = eqFactB wy wyp := by
  have hes : ∀ e ∈ ([wy, ws, wyp] : List V), IsSemiterm LAct 0 e := (List.forall_mem_cons.mpr ⟨hwy, List.forall_mem_cons.mpr ⟨hws, List.forall_mem_cons.mpr ⟨hwyp, List.forall_mem_nil _⟩⟩⟩)
  unfold row_sequentLenFun_as row_sequentLenFun_c
  simp only [List.map_cons, List.map_nil]
  rw [instOuter_subst_listToVec _ isSemiformula_PsetLen (by rfl) _ hes (by row_entriesB), instOuter_subst_listToVec _ isSemiformula_PsetLen (by rfl) _ hes (by row_entriesB), instOuter_subst_listToVec _ isSemiformula_PeqB (by rfl) _ hes (by row_entriesB)]
  all_goals try row_entries_simpB
  row_finish

/-! ## D. Sets: extensionality and `setShift` on a chain (§3.4, §4.5) -/

/-! ### `subsetAntisymm` — `“t s. …”`, `m = 2` -/

noncomputable def row_subsetAntisymm_as : List V := [subst LAct (listToVec [bv 1, bv 0]) Psubset, subst LAct (listToVec [bv 0, bv 1]) Psubset]
noncomputable def row_subsetAntisymm_c : V := subst LAct (listToVec [bv 1, bv 0]) PeqB

theorem quote_row_subsetAntisymm : (⌜Semiformula.lMap emb subsetAntisymmB⌝ : V) = impChain LAct row_subsetAntisymm_as row_subsetAntisymm_c := by
  unfold subsetAntisymmB row_subsetAntisymm_as row_subsetAntisymm_c PeqB Psubset
  all_goals row_shapeB

lemma isSemiformula_subsetAntisymm_c : IsSemiformula LAct ((2 : ℕ) : V) row_subsetAntisymm_c := by
  unfold row_subsetAntisymm_c
  exact isSemiformula_substRow isSemiformula_PeqB _ (by rfl) (by row_entriesB)

/-- `subsetAntisymm` at the witnesses `[ws, wt]` (the DSL variables right-to-left). -/
lemma inst_subsetAntisymm {ws wt : V} (hws : IsSemiterm LAct 0 ws) (hwt : IsSemiterm LAct 0 wt) :
    row_subsetAntisymm_as.map (instOuter LAct [ws, wt]) = [subsetFact ws wt, subsetFact wt ws] ∧
    instOuter LAct [ws, wt] row_subsetAntisymm_c = eqFactB ws wt := by
  have hes : ∀ e ∈ ([ws, wt] : List V), IsSemiterm LAct 0 e := (List.forall_mem_cons.mpr ⟨hws, List.forall_mem_cons.mpr ⟨hwt, List.forall_mem_nil _⟩⟩)
  unfold row_subsetAntisymm_as row_subsetAntisymm_c
  simp only [List.map_cons, List.map_nil]
  rw [instOuter_subst_listToVec _ isSemiformula_Psubset (by rfl) _ hes (by row_entriesB), instOuter_subst_listToVec _ isSemiformula_Psubset (by rfl) _ hes (by row_entriesB), instOuter_subst_listToVec _ isSemiformula_PeqB (by rfl) _ hes (by row_entriesB)]
  all_goals try row_entries_simpB
  row_finish

/-! ### `setShiftInsert` — `“u' u y x s' s. …”`, `m = 6` -/

noncomputable def row_setShiftInsert_as : List V := [subst LAct (listToVec [bv 4, bv 3, bv 5]) Pinsert, subst LAct (listToVec [bv 1, bv 5]) PsetShiftG, subst LAct (listToVec [bv 2, bv 3]) PshiftG, subst LAct (listToVec [bv 0, bv 2, bv 1]) Pinsert]
noncomputable def row_setShiftInsert_c : V := subst LAct (listToVec [bv 0, bv 4]) PsetShiftG

theorem quote_row_setShiftInsert : (⌜Semiformula.lMap emb setShiftInsertB⌝ : V) = impChain LAct row_setShiftInsert_as row_setShiftInsert_c := by
  unfold setShiftInsertB row_setShiftInsert_as row_setShiftInsert_c Pinsert PsetShiftG PshiftG
  all_goals row_shapeB

lemma isSemiformula_setShiftInsert_c : IsSemiformula LAct ((6 : ℕ) : V) row_setShiftInsert_c := by
  unfold row_setShiftInsert_c
  exact isSemiformula_substRow isSemiformula_PsetShiftG _ (by rfl) (by row_entriesB)

/-- `setShiftInsert` at the witnesses `[ws, wsp, wx, wy, wu, wup]` (the DSL variables right-to-left). -/
lemma inst_setShiftInsert {ws wsp wx wy wu wup : V} (hws : IsSemiterm LAct 0 ws) (hwsp : IsSemiterm LAct 0 wsp) (hwx : IsSemiterm LAct 0 wx) (hwy : IsSemiterm LAct 0 wy) (hwu : IsSemiterm LAct 0 wu) (hwup : IsSemiterm LAct 0 wup) :
    row_setShiftInsert_as.map (instOuter LAct [ws, wsp, wx, wy, wu, wup]) = [insFact wsp wx ws, setShiftFact wu ws, shiftFact wy wx, insFact wup wy wu] ∧
    instOuter LAct [ws, wsp, wx, wy, wu, wup] row_setShiftInsert_c = setShiftFact wup wsp := by
  have hes : ∀ e ∈ ([ws, wsp, wx, wy, wu, wup] : List V), IsSemiterm LAct 0 e := (List.forall_mem_cons.mpr ⟨hws, List.forall_mem_cons.mpr ⟨hwsp, List.forall_mem_cons.mpr ⟨hwx, List.forall_mem_cons.mpr ⟨hwy, List.forall_mem_cons.mpr ⟨hwu, List.forall_mem_cons.mpr ⟨hwup, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩)
  unfold row_setShiftInsert_as row_setShiftInsert_c
  simp only [List.map_cons, List.map_nil]
  rw [instOuter_subst_listToVec _ isSemiformula_Pinsert (by rfl) _ hes (by row_entriesB), instOuter_subst_listToVec _ isSemiformula_PsetShiftG (by rfl) _ hes (by row_entriesB), instOuter_subst_listToVec _ isSemiformula_PshiftG (by rfl) _ hes (by row_entriesB), instOuter_subst_listToVec _ isSemiformula_Pinsert (by rfl) _ hes (by row_entriesB), instOuter_subst_listToVec _ isSemiformula_PsetShiftG (by rfl) _ hes (by row_entriesB)]
  all_goals try row_entries_simpB
  row_finish

/-! ### `setShiftEmpty` — `“u. …”`, `m = 1` -/

noncomputable def row_setShiftEmpty_as : List V := [subst LAct (listToVec [bv 0, (𝟎 : V)]) PsetShiftG]
noncomputable def row_setShiftEmpty_c : V := subst LAct (listToVec [bv 0, (𝟎 : V)]) PeqB

theorem quote_row_setShiftEmpty : (⌜Semiformula.lMap emb setShiftEmptyB⌝ : V) = impChain LAct row_setShiftEmpty_as row_setShiftEmpty_c := by
  unfold setShiftEmptyB row_setShiftEmpty_as row_setShiftEmpty_c PeqB PsetShiftG
  all_goals row_shapeB

lemma isSemiformula_setShiftEmpty_c : IsSemiformula LAct ((1 : ℕ) : V) row_setShiftEmpty_c := by
  unfold row_setShiftEmpty_c
  exact isSemiformula_substRow isSemiformula_PeqB _ (by rfl) (by row_entriesB)

/-- `setShiftEmpty` at the witnesses `[wu]` (the DSL variables right-to-left). -/
lemma inst_setShiftEmpty {wu : V} (hwu : IsSemiterm LAct 0 wu) :
    row_setShiftEmpty_as.map (instOuter LAct [wu]) = [setShiftFact wu (𝟎 : V)] ∧
    instOuter LAct [wu] row_setShiftEmpty_c = eqFactB wu (𝟎 : V) := by
  have hes : ∀ e ∈ ([wu] : List V), IsSemiterm LAct 0 e := (List.forall_mem_cons.mpr ⟨hwu, List.forall_mem_nil _⟩)
  unfold row_setShiftEmpty_as row_setShiftEmpty_c
  simp only [List.map_cons, List.map_nil]
  rw [instOuter_subst_listToVec _ isSemiformula_PsetShiftG (by rfl) _ hes (by row_entriesB), instOuter_subst_listToVec _ isSemiformula_PeqB (by rfl) _ hes (by row_entriesB)]
  all_goals try row_entries_simpB
  row_finish

/-! ## E. The ten `fstIdx<Tag>` rows (§4.0 step 2) -/

/-! ### `fstIdxAxL` — `“e p s. …”`, `m = 3` -/

noncomputable def row_fstIdxAxL_as : List V := [subst LAct (listToVec [bv 0, bv 2, bv 1]) PaxL]
noncomputable def row_fstIdxAxL_c : V := subst LAct (listToVec [bv 2, bv 0]) PfstIdx

theorem quote_row_fstIdxAxL : (⌜Semiformula.lMap emb fstIdxAxLB⌝ : V) = impChain LAct row_fstIdxAxL_as row_fstIdxAxL_c := by
  unfold fstIdxAxLB row_fstIdxAxL_as row_fstIdxAxL_c PaxL PfstIdx fstIdxS
  all_goals row_shapeB

lemma isSemiformula_fstIdxAxL_c : IsSemiformula LAct ((3 : ℕ) : V) row_fstIdxAxL_c := by
  unfold row_fstIdxAxL_c
  exact isSemiformula_substRow isSemiformula_PfstIdx _ (by rfl) (by row_entriesB)

/-- `fstIdxAxL` at the witnesses `[ws, wp, we]` (the DSL variables right-to-left). -/
lemma inst_fstIdxAxL {ws wp we : V} (hws : IsSemiterm LAct 0 ws) (hwp : IsSemiterm LAct 0 wp) (hwe : IsSemiterm LAct 0 we) :
    row_fstIdxAxL_as.map (instOuter LAct [ws, wp, we]) = [axLFact we ws wp] ∧
    instOuter LAct [ws, wp, we] row_fstIdxAxL_c = fstIdxFact ws we := by
  have hes : ∀ e ∈ ([ws, wp, we] : List V), IsSemiterm LAct 0 e := (List.forall_mem_cons.mpr ⟨hws, List.forall_mem_cons.mpr ⟨hwp, List.forall_mem_cons.mpr ⟨hwe, List.forall_mem_nil _⟩⟩⟩)
  unfold row_fstIdxAxL_as row_fstIdxAxL_c
  simp only [List.map_cons, List.map_nil]
  rw [instOuter_subst_listToVec _ isSemiformula_PaxL (by rfl) _ hes (by row_entriesB), instOuter_subst_listToVec _ isSemiformula_PfstIdx (by rfl) _ hes (by row_entriesB)]
  all_goals try row_entries_simpB
  row_finish

/-! ### `fstIdxVerum` — `“e s. …”`, `m = 2` -/

noncomputable def row_fstIdxVerum_as : List V := [subst LAct (listToVec [bv 0, bv 1]) PverumIntro]
noncomputable def row_fstIdxVerum_c : V := subst LAct (listToVec [bv 1, bv 0]) PfstIdx

theorem quote_row_fstIdxVerum : (⌜Semiformula.lMap emb fstIdxVerumB⌝ : V) = impChain LAct row_fstIdxVerum_as row_fstIdxVerum_c := by
  unfold fstIdxVerumB row_fstIdxVerum_as row_fstIdxVerum_c PfstIdx PverumIntro fstIdxS
  all_goals row_shapeB

lemma isSemiformula_fstIdxVerum_c : IsSemiformula LAct ((2 : ℕ) : V) row_fstIdxVerum_c := by
  unfold row_fstIdxVerum_c
  exact isSemiformula_substRow isSemiformula_PfstIdx _ (by rfl) (by row_entriesB)

/-- `fstIdxVerum` at the witnesses `[ws, we]` (the DSL variables right-to-left). -/
lemma inst_fstIdxVerum {ws we : V} (hws : IsSemiterm LAct 0 ws) (hwe : IsSemiterm LAct 0 we) :
    row_fstIdxVerum_as.map (instOuter LAct [ws, we]) = [verumIntroFact we ws] ∧
    instOuter LAct [ws, we] row_fstIdxVerum_c = fstIdxFact ws we := by
  have hes : ∀ e ∈ ([ws, we] : List V), IsSemiterm LAct 0 e := (List.forall_mem_cons.mpr ⟨hws, List.forall_mem_cons.mpr ⟨hwe, List.forall_mem_nil _⟩⟩)
  unfold row_fstIdxVerum_as row_fstIdxVerum_c
  simp only [List.map_cons, List.map_nil]
  rw [instOuter_subst_listToVec _ isSemiformula_PverumIntro (by rfl) _ hes (by row_entriesB), instOuter_subst_listToVec _ isSemiformula_PfstIdx (by rfl) _ hes (by row_entriesB)]
  all_goals try row_entries_simpB
  row_finish

/-! ### `fstIdxAnd` — `“e dq dp q p s. …”`, `m = 6` -/

noncomputable def row_fstIdxAnd_as : List V := [subst LAct (listToVec [bv 0, bv 5, bv 4, bv 3, bv 2, bv 1]) PandIntro]
noncomputable def row_fstIdxAnd_c : V := subst LAct (listToVec [bv 5, bv 0]) PfstIdx

theorem quote_row_fstIdxAnd : (⌜Semiformula.lMap emb fstIdxAndB⌝ : V) = impChain LAct row_fstIdxAnd_as row_fstIdxAnd_c := by
  unfold fstIdxAndB row_fstIdxAnd_as row_fstIdxAnd_c PandIntro PfstIdx fstIdxS
  all_goals row_shapeB

lemma isSemiformula_fstIdxAnd_c : IsSemiformula LAct ((6 : ℕ) : V) row_fstIdxAnd_c := by
  unfold row_fstIdxAnd_c
  exact isSemiformula_substRow isSemiformula_PfstIdx _ (by rfl) (by row_entriesB)

/-- `fstIdxAnd` at the witnesses `[ws, wp, wq, wdp, wdq, we]` (the DSL variables right-to-left). -/
lemma inst_fstIdxAnd {ws wp wq wdp wdq we : V} (hws : IsSemiterm LAct 0 ws) (hwp : IsSemiterm LAct 0 wp) (hwq : IsSemiterm LAct 0 wq) (hwdp : IsSemiterm LAct 0 wdp) (hwdq : IsSemiterm LAct 0 wdq) (hwe : IsSemiterm LAct 0 we) :
    row_fstIdxAnd_as.map (instOuter LAct [ws, wp, wq, wdp, wdq, we]) = [andIntroFact we ws wp wq wdp wdq] ∧
    instOuter LAct [ws, wp, wq, wdp, wdq, we] row_fstIdxAnd_c = fstIdxFact ws we := by
  have hes : ∀ e ∈ ([ws, wp, wq, wdp, wdq, we] : List V), IsSemiterm LAct 0 e := (List.forall_mem_cons.mpr ⟨hws, List.forall_mem_cons.mpr ⟨hwp, List.forall_mem_cons.mpr ⟨hwq, List.forall_mem_cons.mpr ⟨hwdp, List.forall_mem_cons.mpr ⟨hwdq, List.forall_mem_cons.mpr ⟨hwe, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩)
  unfold row_fstIdxAnd_as row_fstIdxAnd_c
  simp only [List.map_cons, List.map_nil]
  rw [instOuter_subst_listToVec _ isSemiformula_PandIntro (by rfl) _ hes (by row_entriesB), instOuter_subst_listToVec _ isSemiformula_PfstIdx (by rfl) _ hes (by row_entriesB)]
  all_goals try row_entries_simpB
  row_finish

/-! ### `fstIdxOr` — `“e d q p s. …”`, `m = 5` -/

noncomputable def row_fstIdxOr_as : List V := [subst LAct (listToVec [bv 0, bv 4, bv 3, bv 2, bv 1]) PorIntro]
noncomputable def row_fstIdxOr_c : V := subst LAct (listToVec [bv 4, bv 0]) PfstIdx

theorem quote_row_fstIdxOr : (⌜Semiformula.lMap emb fstIdxOrB⌝ : V) = impChain LAct row_fstIdxOr_as row_fstIdxOr_c := by
  unfold fstIdxOrB row_fstIdxOr_as row_fstIdxOr_c PfstIdx PorIntro fstIdxS
  all_goals row_shapeB

lemma isSemiformula_fstIdxOr_c : IsSemiformula LAct ((5 : ℕ) : V) row_fstIdxOr_c := by
  unfold row_fstIdxOr_c
  exact isSemiformula_substRow isSemiformula_PfstIdx _ (by rfl) (by row_entriesB)

/-- `fstIdxOr` at the witnesses `[ws, wp, wq, wd, we]` (the DSL variables right-to-left). -/
lemma inst_fstIdxOr {ws wp wq wd we : V} (hws : IsSemiterm LAct 0 ws) (hwp : IsSemiterm LAct 0 wp) (hwq : IsSemiterm LAct 0 wq) (hwd : IsSemiterm LAct 0 wd) (hwe : IsSemiterm LAct 0 we) :
    row_fstIdxOr_as.map (instOuter LAct [ws, wp, wq, wd, we]) = [orIntroFact we ws wp wq wd] ∧
    instOuter LAct [ws, wp, wq, wd, we] row_fstIdxOr_c = fstIdxFact ws we := by
  have hes : ∀ e ∈ ([ws, wp, wq, wd, we] : List V), IsSemiterm LAct 0 e := (List.forall_mem_cons.mpr ⟨hws, List.forall_mem_cons.mpr ⟨hwp, List.forall_mem_cons.mpr ⟨hwq, List.forall_mem_cons.mpr ⟨hwd, List.forall_mem_cons.mpr ⟨hwe, List.forall_mem_nil _⟩⟩⟩⟩⟩)
  unfold row_fstIdxOr_as row_fstIdxOr_c
  simp only [List.map_cons, List.map_nil]
  rw [instOuter_subst_listToVec _ isSemiformula_PorIntro (by rfl) _ hes (by row_entriesB), instOuter_subst_listToVec _ isSemiformula_PfstIdx (by rfl) _ hes (by row_entriesB)]
  all_goals try row_entries_simpB
  row_finish

/-! ### `fstIdxAll` — `“e d p s. …”`, `m = 4` -/

noncomputable def row_fstIdxAll_as : List V := [subst LAct (listToVec [bv 0, bv 3, bv 2, bv 1]) PallIntro]
noncomputable def row_fstIdxAll_c : V := subst LAct (listToVec [bv 3, bv 0]) PfstIdx

theorem quote_row_fstIdxAll : (⌜Semiformula.lMap emb fstIdxAllB⌝ : V) = impChain LAct row_fstIdxAll_as row_fstIdxAll_c := by
  unfold fstIdxAllB row_fstIdxAll_as row_fstIdxAll_c PallIntro PfstIdx fstIdxS
  all_goals row_shapeB

lemma isSemiformula_fstIdxAll_c : IsSemiformula LAct ((4 : ℕ) : V) row_fstIdxAll_c := by
  unfold row_fstIdxAll_c
  exact isSemiformula_substRow isSemiformula_PfstIdx _ (by rfl) (by row_entriesB)

/-- `fstIdxAll` at the witnesses `[ws, wp, wd, we]` (the DSL variables right-to-left). -/
lemma inst_fstIdxAll {ws wp wd we : V} (hws : IsSemiterm LAct 0 ws) (hwp : IsSemiterm LAct 0 wp) (hwd : IsSemiterm LAct 0 wd) (hwe : IsSemiterm LAct 0 we) :
    row_fstIdxAll_as.map (instOuter LAct [ws, wp, wd, we]) = [allIntroFact we ws wp wd] ∧
    instOuter LAct [ws, wp, wd, we] row_fstIdxAll_c = fstIdxFact ws we := by
  have hes : ∀ e ∈ ([ws, wp, wd, we] : List V), IsSemiterm LAct 0 e := (List.forall_mem_cons.mpr ⟨hws, List.forall_mem_cons.mpr ⟨hwp, List.forall_mem_cons.mpr ⟨hwd, List.forall_mem_cons.mpr ⟨hwe, List.forall_mem_nil _⟩⟩⟩⟩)
  unfold row_fstIdxAll_as row_fstIdxAll_c
  simp only [List.map_cons, List.map_nil]
  rw [instOuter_subst_listToVec _ isSemiformula_PallIntro (by rfl) _ hes (by row_entriesB), instOuter_subst_listToVec _ isSemiformula_PfstIdx (by rfl) _ hes (by row_entriesB)]
  all_goals try row_entries_simpB
  row_finish

/-! ### `fstIdxExs` — `“e d t p s. …”`, `m = 5` -/

noncomputable def row_fstIdxExs_as : List V := [subst LAct (listToVec [bv 0, bv 4, bv 3, bv 2, bv 1]) PexsIntro]
noncomputable def row_fstIdxExs_c : V := subst LAct (listToVec [bv 4, bv 0]) PfstIdx

theorem quote_row_fstIdxExs : (⌜Semiformula.lMap emb fstIdxExsB⌝ : V) = impChain LAct row_fstIdxExs_as row_fstIdxExs_c := by
  unfold fstIdxExsB row_fstIdxExs_as row_fstIdxExs_c PexsIntro PfstIdx fstIdxS
  all_goals row_shapeB

lemma isSemiformula_fstIdxExs_c : IsSemiformula LAct ((5 : ℕ) : V) row_fstIdxExs_c := by
  unfold row_fstIdxExs_c
  exact isSemiformula_substRow isSemiformula_PfstIdx _ (by rfl) (by row_entriesB)

/-- `fstIdxExs` at the witnesses `[ws, wp, wt, wd, we]` (the DSL variables right-to-left). -/
lemma inst_fstIdxExs {ws wp wt wd we : V} (hws : IsSemiterm LAct 0 ws) (hwp : IsSemiterm LAct 0 wp) (hwt : IsSemiterm LAct 0 wt) (hwd : IsSemiterm LAct 0 wd) (hwe : IsSemiterm LAct 0 we) :
    row_fstIdxExs_as.map (instOuter LAct [ws, wp, wt, wd, we]) = [exsIntroFact we ws wp wt wd] ∧
    instOuter LAct [ws, wp, wt, wd, we] row_fstIdxExs_c = fstIdxFact ws we := by
  have hes : ∀ e ∈ ([ws, wp, wt, wd, we] : List V), IsSemiterm LAct 0 e := (List.forall_mem_cons.mpr ⟨hws, List.forall_mem_cons.mpr ⟨hwp, List.forall_mem_cons.mpr ⟨hwt, List.forall_mem_cons.mpr ⟨hwd, List.forall_mem_cons.mpr ⟨hwe, List.forall_mem_nil _⟩⟩⟩⟩⟩)
  unfold row_fstIdxExs_as row_fstIdxExs_c
  simp only [List.map_cons, List.map_nil]
  rw [instOuter_subst_listToVec _ isSemiformula_PexsIntro (by rfl) _ hes (by row_entriesB), instOuter_subst_listToVec _ isSemiformula_PfstIdx (by rfl) _ hes (by row_entriesB)]
  all_goals try row_entries_simpB
  row_finish

/-! ### `fstIdxWk` — `“e d s. …”`, `m = 3` -/

noncomputable def row_fstIdxWk_as : List V := [subst LAct (listToVec [bv 0, bv 2, bv 1]) PwkRule]
noncomputable def row_fstIdxWk_c : V := subst LAct (listToVec [bv 2, bv 0]) PfstIdx

theorem quote_row_fstIdxWk : (⌜Semiformula.lMap emb fstIdxWkB⌝ : V) = impChain LAct row_fstIdxWk_as row_fstIdxWk_c := by
  unfold fstIdxWkB row_fstIdxWk_as row_fstIdxWk_c PfstIdx PwkRule fstIdxS
  all_goals row_shapeB

lemma isSemiformula_fstIdxWk_c : IsSemiformula LAct ((3 : ℕ) : V) row_fstIdxWk_c := by
  unfold row_fstIdxWk_c
  exact isSemiformula_substRow isSemiformula_PfstIdx _ (by rfl) (by row_entriesB)

/-- `fstIdxWk` at the witnesses `[ws, wd, we]` (the DSL variables right-to-left). -/
lemma inst_fstIdxWk {ws wd we : V} (hws : IsSemiterm LAct 0 ws) (hwd : IsSemiterm LAct 0 wd) (hwe : IsSemiterm LAct 0 we) :
    row_fstIdxWk_as.map (instOuter LAct [ws, wd, we]) = [wkRuleFact we ws wd] ∧
    instOuter LAct [ws, wd, we] row_fstIdxWk_c = fstIdxFact ws we := by
  have hes : ∀ e ∈ ([ws, wd, we] : List V), IsSemiterm LAct 0 e := (List.forall_mem_cons.mpr ⟨hws, List.forall_mem_cons.mpr ⟨hwd, List.forall_mem_cons.mpr ⟨hwe, List.forall_mem_nil _⟩⟩⟩)
  unfold row_fstIdxWk_as row_fstIdxWk_c
  simp only [List.map_cons, List.map_nil]
  rw [instOuter_subst_listToVec _ isSemiformula_PwkRule (by rfl) _ hes (by row_entriesB), instOuter_subst_listToVec _ isSemiformula_PfstIdx (by rfl) _ hes (by row_entriesB)]
  all_goals try row_entries_simpB
  row_finish

/-! ### `fstIdxShift` — `“e d s. …”`, `m = 3` -/

noncomputable def row_fstIdxShift_as : List V := [subst LAct (listToVec [bv 0, bv 2, bv 1]) PshiftRule]
noncomputable def row_fstIdxShift_c : V := subst LAct (listToVec [bv 2, bv 0]) PfstIdx

theorem quote_row_fstIdxShift : (⌜Semiformula.lMap emb fstIdxShiftB⌝ : V) = impChain LAct row_fstIdxShift_as row_fstIdxShift_c := by
  unfold fstIdxShiftB row_fstIdxShift_as row_fstIdxShift_c PfstIdx PshiftRule fstIdxS
  all_goals row_shapeB

lemma isSemiformula_fstIdxShift_c : IsSemiformula LAct ((3 : ℕ) : V) row_fstIdxShift_c := by
  unfold row_fstIdxShift_c
  exact isSemiformula_substRow isSemiformula_PfstIdx _ (by rfl) (by row_entriesB)

/-- `fstIdxShift` at the witnesses `[ws, wd, we]` (the DSL variables right-to-left). -/
lemma inst_fstIdxShift {ws wd we : V} (hws : IsSemiterm LAct 0 ws) (hwd : IsSemiterm LAct 0 wd) (hwe : IsSemiterm LAct 0 we) :
    row_fstIdxShift_as.map (instOuter LAct [ws, wd, we]) = [shiftRuleFact we ws wd] ∧
    instOuter LAct [ws, wd, we] row_fstIdxShift_c = fstIdxFact ws we := by
  have hes : ∀ e ∈ ([ws, wd, we] : List V), IsSemiterm LAct 0 e := (List.forall_mem_cons.mpr ⟨hws, List.forall_mem_cons.mpr ⟨hwd, List.forall_mem_cons.mpr ⟨hwe, List.forall_mem_nil _⟩⟩⟩)
  unfold row_fstIdxShift_as row_fstIdxShift_c
  simp only [List.map_cons, List.map_nil]
  rw [instOuter_subst_listToVec _ isSemiformula_PshiftRule (by rfl) _ hes (by row_entriesB), instOuter_subst_listToVec _ isSemiformula_PfstIdx (by rfl) _ hes (by row_entriesB)]
  all_goals try row_entries_simpB
  row_finish

/-! ### `fstIdxCut` — `“e d₂ d₁ p s. …”`, `m = 5` -/

noncomputable def row_fstIdxCut_as : List V := [subst LAct (listToVec [bv 0, bv 4, bv 3, bv 2, bv 1]) PcutRule]
noncomputable def row_fstIdxCut_c : V := subst LAct (listToVec [bv 4, bv 0]) PfstIdx

theorem quote_row_fstIdxCut : (⌜Semiformula.lMap emb fstIdxCutB⌝ : V) = impChain LAct row_fstIdxCut_as row_fstIdxCut_c := by
  unfold fstIdxCutB row_fstIdxCut_as row_fstIdxCut_c PcutRule PfstIdx fstIdxS
  all_goals row_shapeB

lemma isSemiformula_fstIdxCut_c : IsSemiformula LAct ((5 : ℕ) : V) row_fstIdxCut_c := by
  unfold row_fstIdxCut_c
  exact isSemiformula_substRow isSemiformula_PfstIdx _ (by rfl) (by row_entriesB)

/-- `fstIdxCut` at the witnesses `[ws, wp, wd1, wd2, we]` (the DSL variables right-to-left). -/
lemma inst_fstIdxCut {ws wp wd1 wd2 we : V} (hws : IsSemiterm LAct 0 ws) (hwp : IsSemiterm LAct 0 wp) (hwd1 : IsSemiterm LAct 0 wd1) (hwd2 : IsSemiterm LAct 0 wd2) (hwe : IsSemiterm LAct 0 we) :
    row_fstIdxCut_as.map (instOuter LAct [ws, wp, wd1, wd2, we]) = [cutRuleFact we ws wp wd1 wd2] ∧
    instOuter LAct [ws, wp, wd1, wd2, we] row_fstIdxCut_c = fstIdxFact ws we := by
  have hes : ∀ e ∈ ([ws, wp, wd1, wd2, we] : List V), IsSemiterm LAct 0 e := (List.forall_mem_cons.mpr ⟨hws, List.forall_mem_cons.mpr ⟨hwp, List.forall_mem_cons.mpr ⟨hwd1, List.forall_mem_cons.mpr ⟨hwd2, List.forall_mem_cons.mpr ⟨hwe, List.forall_mem_nil _⟩⟩⟩⟩⟩)
  unfold row_fstIdxCut_as row_fstIdxCut_c
  simp only [List.map_cons, List.map_nil]
  rw [instOuter_subst_listToVec _ isSemiformula_PcutRule (by rfl) _ hes (by row_entriesB), instOuter_subst_listToVec _ isSemiformula_PfstIdx (by rfl) _ hes (by row_entriesB)]
  all_goals try row_entries_simpB
  row_finish

/-! ### `fstIdxAxm` — `“e p s. …”`, `m = 3` -/

noncomputable def row_fstIdxAxm_as : List V := [subst LAct (listToVec [bv 0, bv 2, bv 1]) Paxm]
noncomputable def row_fstIdxAxm_c : V := subst LAct (listToVec [bv 2, bv 0]) PfstIdx

theorem quote_row_fstIdxAxm : (⌜Semiformula.lMap emb fstIdxAxmB⌝ : V) = impChain LAct row_fstIdxAxm_as row_fstIdxAxm_c := by
  unfold fstIdxAxmB row_fstIdxAxm_as row_fstIdxAxm_c Paxm PfstIdx fstIdxS
  all_goals row_shapeB

lemma isSemiformula_fstIdxAxm_c : IsSemiformula LAct ((3 : ℕ) : V) row_fstIdxAxm_c := by
  unfold row_fstIdxAxm_c
  exact isSemiformula_substRow isSemiformula_PfstIdx _ (by rfl) (by row_entriesB)

/-- `fstIdxAxm` at the witnesses `[ws, wp, we]` (the DSL variables right-to-left). -/
lemma inst_fstIdxAxm {ws wp we : V} (hws : IsSemiterm LAct 0 ws) (hwp : IsSemiterm LAct 0 wp) (hwe : IsSemiterm LAct 0 we) :
    row_fstIdxAxm_as.map (instOuter LAct [ws, wp, we]) = [axmFact we ws wp] ∧
    instOuter LAct [ws, wp, we] row_fstIdxAxm_c = fstIdxFact ws we := by
  have hes : ∀ e ∈ ([ws, wp, we] : List V), IsSemiterm LAct 0 e := (List.forall_mem_cons.mpr ⟨hws, List.forall_mem_cons.mpr ⟨hwp, List.forall_mem_cons.mpr ⟨hwe, List.forall_mem_nil _⟩⟩⟩)
  unfold row_fstIdxAxm_as row_fstIdxAxm_c
  simp only [List.map_cons, List.map_nil]
  rw [instOuter_subst_listToVec _ isSemiformula_Paxm (by rfl) _ hes (by row_entriesB), instOuter_subst_listToVec _ isSemiformula_PfstIdx (by rfl) _ hes (by row_entriesB)]
  all_goals try row_entries_simpB
  row_finish

/-! ## F. The top: `proofLenDef`, `proof`, `instB`, `gBudget`, `‖·‖`, the `binNumeral` certification (§7.1) -/

/-! ### `proofLenDefIntro` — `“n d. …”`, `m = 2` -/

noncomputable def row_proofLenDefIntro_as : List V := [subst LAct (listToVec [bv 1]) Pderiv, subst LAct (listToVec [bv 1, bv 0]) Pdlen]
noncomputable def row_proofLenDefIntro_c : V := subst LAct (listToVec [bv 0, bv 1]) PdlenDef

theorem quote_row_proofLenDefIntro : (⌜Semiformula.lMap emb proofLenDefIntroB⌝ : V) = impChain LAct row_proofLenDefIntro_as row_proofLenDefIntro_c := by
  unfold proofLenDefIntroB row_proofLenDefIntro_as row_proofLenDefIntro_c Pderiv Pdlen PdlenDef derivS proofLenS
  all_goals row_shapeB

lemma isSemiformula_proofLenDefIntro_c : IsSemiformula LAct ((2 : ℕ) : V) row_proofLenDefIntro_c := by
  unfold row_proofLenDefIntro_c
  exact isSemiformula_substRow isSemiformula_PdlenDef _ (by rfl) (by row_entriesB)

/-- `proofLenDefIntro` at the witnesses `[wd, wn]` (the DSL variables right-to-left). -/
lemma inst_proofLenDefIntro {wd wn : V} (hwd : IsSemiterm LAct 0 wd) (hwn : IsSemiterm LAct 0 wn) :
    row_proofLenDefIntro_as.map (instOuter LAct [wd, wn]) = [derFact wd, proofLenFact wd wn] ∧
    instOuter LAct [wd, wn] row_proofLenDefIntro_c = proofLenDefFact wn wd := by
  have hes : ∀ e ∈ ([wd, wn] : List V), IsSemiterm LAct 0 e := (List.forall_mem_cons.mpr ⟨hwd, List.forall_mem_cons.mpr ⟨hwn, List.forall_mem_nil _⟩⟩)
  unfold row_proofLenDefIntro_as row_proofLenDefIntro_c
  simp only [List.map_cons, List.map_nil]
  rw [instOuter_subst_listToVec _ isSemiformula_Pderiv (by rfl) _ hes (by row_entriesB), instOuter_subst_listToVec _ isSemiformula_Pdlen (by rfl) _ hes (by row_entriesB), instOuter_subst_listToVec _ isSemiformula_PdlenDef (by rfl) _ hes (by row_entriesB)]
  all_goals try row_entries_simpB
  row_finish

/-! ### `proofIntro` — `“d g s. …”`, `m = 3` -/

noncomputable def row_proofIntro_as : List V := [subst LAct (listToVec [bv 2, bv 1, (𝟎 : V)]) Pinsert, subst LAct (listToVec [bv 2, bv 0]) PfstIdx, subst LAct (listToVec [bv 0]) Pderiv]
noncomputable def row_proofIntro_c : V := subst LAct (listToVec [bv 0, bv 1]) Pproof

theorem quote_row_proofIntro : (⌜Semiformula.lMap emb proofIntroB⌝ : V) = impChain LAct row_proofIntro_as row_proofIntro_c := by
  unfold proofIntroB row_proofIntro_as row_proofIntro_c Pderiv PfstIdx Pinsert Pproof derivS fstIdxS
  all_goals row_shapeB

lemma isSemiformula_proofIntro_c : IsSemiformula LAct ((3 : ℕ) : V) row_proofIntro_c := by
  unfold row_proofIntro_c
  exact isSemiformula_substRow isSemiformula_Pproof _ (by rfl) (by row_entriesB)

/-- `proofIntro` at the witnesses `[ws, wg, wd]` (the DSL variables right-to-left). -/
lemma inst_proofIntro {ws wg wd : V} (hws : IsSemiterm LAct 0 ws) (hwg : IsSemiterm LAct 0 wg) (hwd : IsSemiterm LAct 0 wd) :
    row_proofIntro_as.map (instOuter LAct [ws, wg, wd]) = [insFact ws wg (𝟎 : V), fstIdxFact ws wd, derFact wd] ∧
    instOuter LAct [ws, wg, wd] row_proofIntro_c = proofFact wd wg := by
  have hes : ∀ e ∈ ([ws, wg, wd] : List V), IsSemiterm LAct 0 e := (List.forall_mem_cons.mpr ⟨hws, List.forall_mem_cons.mpr ⟨hwg, List.forall_mem_cons.mpr ⟨hwd, List.forall_mem_nil _⟩⟩⟩)
  unfold row_proofIntro_as row_proofIntro_c
  simp only [List.map_cons, List.map_nil]
  rw [instOuter_subst_listToVec _ isSemiformula_Pinsert (by rfl) _ hes (by row_entriesB), instOuter_subst_listToVec _ isSemiformula_PfstIdx (by rfl) _ hes (by row_entriesB), instOuter_subst_listToVec _ isSemiformula_Pderiv (by rfl) _ hes (by row_entriesB), instOuter_subst_listToVec _ isSemiformula_Pproof (by rfl) _ hes (by row_entriesB)]
  all_goals try row_entries_simpB
  row_finish

/-! ### `instBIntro` — `“g v t k n. …”`, `m = 5` -/

noncomputable def row_instBIntro_as : List V := [subst LAct (listToVec [bv 2, bv 3]) Pbnum, subst LAct (listToVec [bv 1, bv 2, (𝟎 : V)]) Padjoin, subst LAct (listToVec [bv 0, bv 1, bv 4]) PsubstsG]
noncomputable def row_instBIntro_c : V := subst LAct (listToVec [bv 0, bv 4, bv 3]) PinstB

theorem quote_row_instBIntro : (⌜Semiformula.lMap emb instBIntroB⌝ : V) = impChain LAct row_instBIntro_as row_instBIntro_c := by
  unfold instBIntroB row_instBIntro_as row_instBIntro_c Padjoin Pbnum PinstB PsubstsG
  all_goals row_shapeB

lemma isSemiformula_instBIntro_c : IsSemiformula LAct ((5 : ℕ) : V) row_instBIntro_c := by
  unfold row_instBIntro_c
  exact isSemiformula_substRow isSemiformula_PinstB _ (by rfl) (by row_entriesB)

/-- `instBIntro` at the witnesses `[wn, wk, wt, wv, wg]` (the DSL variables right-to-left). -/
lemma inst_instBIntro {wn wk wt wv wg : V} (hwn : IsSemiterm LAct 0 wn) (hwk : IsSemiterm LAct 0 wk) (hwt : IsSemiterm LAct 0 wt) (hwv : IsSemiterm LAct 0 wv) (hwg : IsSemiterm LAct 0 wg) :
    row_instBIntro_as.map (instOuter LAct [wn, wk, wt, wv, wg]) = [binNumeralFact wt wk, adjFact wv wt (𝟎 : V), substFact wg wv wn] ∧
    instOuter LAct [wn, wk, wt, wv, wg] row_instBIntro_c = instBFact wg wn wk := by
  have hes : ∀ e ∈ ([wn, wk, wt, wv, wg] : List V), IsSemiterm LAct 0 e := (List.forall_mem_cons.mpr ⟨hwn, List.forall_mem_cons.mpr ⟨hwk, List.forall_mem_cons.mpr ⟨hwt, List.forall_mem_cons.mpr ⟨hwv, List.forall_mem_cons.mpr ⟨hwg, List.forall_mem_nil _⟩⟩⟩⟩⟩)
  unfold row_instBIntro_as row_instBIntro_c
  simp only [List.map_cons, List.map_nil]
  rw [instOuter_subst_listToVec _ isSemiformula_Pbnum (by rfl) _ hes (by row_entriesB), instOuter_subst_listToVec _ isSemiformula_Padjoin (by rfl) _ hes (by row_entriesB), instOuter_subst_listToVec _ isSemiformula_PsubstsG (by rfl) _ hes (by row_entriesB), instOuter_subst_listToVec _ isSemiformula_PinstB (by rfl) _ hes (by row_entriesB)]
  all_goals try row_entries_simpB
  row_finish

/-! ### `binNumeralZeroCert` — `“t. …”`, `m = 1` -/

noncomputable def row_binNumeralZeroCert_as : List V := [subst LAct (listToVec [bv 0, (𝟎 : V), (𝟎 : V), (𝟎 : V)]) Pfunc]
noncomputable def row_binNumeralZeroCert_c : V := subst LAct (listToVec [bv 0, (𝟎 : V)]) Pbnum

theorem quote_row_binNumeralZeroCert : (⌜Semiformula.lMap emb binNumeralZeroCertB⌝ : V) = impChain LAct row_binNumeralZeroCert_as row_binNumeralZeroCert_c := by
  unfold binNumeralZeroCertB row_binNumeralZeroCert_as row_binNumeralZeroCert_c Pbnum Pfunc
  all_goals row_shapeB

lemma isSemiformula_binNumeralZeroCert_c : IsSemiformula LAct ((1 : ℕ) : V) row_binNumeralZeroCert_c := by
  unfold row_binNumeralZeroCert_c
  exact isSemiformula_substRow isSemiformula_Pbnum _ (by rfl) (by row_entriesB)

/-- `binNumeralZeroCert` at the witnesses `[wt]` (the DSL variables right-to-left). -/
lemma inst_binNumeralZeroCert {wt : V} (hwt : IsSemiterm LAct 0 wt) :
    row_binNumeralZeroCert_as.map (instOuter LAct [wt]) = [funcFact wt (𝟎 : V) (𝟎 : V) (𝟎 : V)] ∧
    instOuter LAct [wt] row_binNumeralZeroCert_c = binNumeralFact wt (𝟎 : V) := by
  have hes : ∀ e ∈ ([wt] : List V), IsSemiterm LAct 0 e := (List.forall_mem_cons.mpr ⟨hwt, List.forall_mem_nil _⟩)
  unfold row_binNumeralZeroCert_as row_binNumeralZeroCert_c
  simp only [List.map_cons, List.map_nil]
  rw [instOuter_subst_listToVec _ isSemiformula_Pfunc (by rfl) _ hes (by row_entriesB), instOuter_subst_listToVec _ isSemiformula_Pbnum (by rfl) _ hes (by row_entriesB)]
  all_goals try row_entries_simpB
  row_finish

/-! ### `binNumeralOneCert` — `“t. …”`, `m = 1` -/

noncomputable def row_binNumeralOneCert_as : List V := [subst LAct (listToVec [bv 0, (𝟎 : V), cT 1, (𝟎 : V)]) Pfunc]
noncomputable def row_binNumeralOneCert_c : V := subst LAct (listToVec [bv 0, (𝟏 : V)]) Pbnum

theorem quote_row_binNumeralOneCert : (⌜Semiformula.lMap emb binNumeralOneCertB⌝ : V) = impChain LAct row_binNumeralOneCert_as row_binNumeralOneCert_c := by
  unfold binNumeralOneCertB row_binNumeralOneCert_as row_binNumeralOneCert_c Pbnum Pfunc
  all_goals row_shapeB

lemma isSemiformula_binNumeralOneCert_c : IsSemiformula LAct ((1 : ℕ) : V) row_binNumeralOneCert_c := by
  unfold row_binNumeralOneCert_c
  exact isSemiformula_substRow isSemiformula_Pbnum _ (by rfl) (by row_entriesB)

/-- `binNumeralOneCert` at the witnesses `[wt]` (the DSL variables right-to-left). -/
lemma inst_binNumeralOneCert {wt : V} (hwt : IsSemiterm LAct 0 wt) :
    row_binNumeralOneCert_as.map (instOuter LAct [wt]) = [funcFact wt (𝟎 : V) (cT 1) (𝟎 : V)] ∧
    instOuter LAct [wt] row_binNumeralOneCert_c = binNumeralFact wt (𝟏 : V) := by
  have hes : ∀ e ∈ ([wt] : List V), IsSemiterm LAct 0 e := (List.forall_mem_cons.mpr ⟨hwt, List.forall_mem_nil _⟩)
  unfold row_binNumeralOneCert_as row_binNumeralOneCert_c
  simp only [List.map_cons, List.map_nil]
  rw [instOuter_subst_listToVec _ isSemiformula_Pfunc (by rfl) _ hes (by row_entriesB), instOuter_subst_listToVec _ isSemiformula_Pbnum (by rfl) _ hes (by row_entriesB)]
  all_goals try row_entries_simpB
  row_finish

/-! ### `binNumeralEvenCert` — `“u v v' two w w' one t m. …”`, `m = 9` -/

noncomputable def row_binNumeralEvenCert_as : List V := [subst LAct (listToVec [(𝟏 : V), bv 8]) Ple, subst LAct (listToVec [bv 7, bv 8]) Pbnum, subst LAct (listToVec [bv 6, (𝟎 : V), cT 1, (𝟎 : V)]) Pfunc, subst LAct (listToVec [bv 5, bv 6, (𝟎 : V)]) Padjoin, subst LAct (listToVec [bv 4, bv 6, bv 5]) Padjoin, subst LAct (listToVec [bv 3, cT 2, (𝟎 : V), bv 4]) Pfunc, subst LAct (listToVec [bv 2, bv 7, (𝟎 : V)]) Padjoin, subst LAct (listToVec [bv 1, bv 3, bv 2]) Padjoin, subst LAct (listToVec [bv 0, cT 2, cT 1, bv 1]) Pfunc]
noncomputable def row_binNumeralEvenCert_c : V := subst LAct (listToVec [bv 0, (((𝟏 : V) ^+ (𝟏 : V)) ^* bv 8)]) Pbnum

theorem quote_row_binNumeralEvenCert : (⌜Semiformula.lMap emb binNumeralEvenCertB⌝ : V) = impChain LAct row_binNumeralEvenCert_as row_binNumeralEvenCert_c := by
  unfold binNumeralEvenCertB row_binNumeralEvenCert_as row_binNumeralEvenCert_c Padjoin Pbnum Pfunc Ple leS
  all_goals row_shapeB

lemma isSemiformula_binNumeralEvenCert_c : IsSemiformula LAct ((9 : ℕ) : V) row_binNumeralEvenCert_c := by
  unfold row_binNumeralEvenCert_c
  exact isSemiformula_substRow isSemiformula_Pbnum _ (by rfl) (by row_entriesB)

/-- `binNumeralEvenCert` at the witnesses `[wm, wt, wone, wwp, ww, wtwo, wvp, wv, wu]` (the DSL variables right-to-left). -/
lemma inst_binNumeralEvenCert {wm wt wone wwp ww wtwo wvp wv wu : V} (hwm : IsSemiterm LAct 0 wm) (hwt : IsSemiterm LAct 0 wt) (hwone : IsSemiterm LAct 0 wone) (hwwp : IsSemiterm LAct 0 wwp) (hww : IsSemiterm LAct 0 ww) (hwtwo : IsSemiterm LAct 0 wtwo) (hwvp : IsSemiterm LAct 0 wvp) (hwv : IsSemiterm LAct 0 wv) (hwu : IsSemiterm LAct 0 wu) :
    row_binNumeralEvenCert_as.map (instOuter LAct [wm, wt, wone, wwp, ww, wtwo, wvp, wv, wu]) = [leFact (𝟏 : V) wm, binNumeralFact wt wm, funcFact wone (𝟎 : V) (cT 1) (𝟎 : V), adjFact wwp wone (𝟎 : V), adjFact ww wone wwp, funcFact wtwo (cT 2) (𝟎 : V) ww, adjFact wvp wt (𝟎 : V), adjFact wv wtwo wvp, funcFact wu (cT 2) (cT 1) wv] ∧
    instOuter LAct [wm, wt, wone, wwp, ww, wtwo, wvp, wv, wu] row_binNumeralEvenCert_c = binNumeralFact wu (((𝟏 : V) ^+ (𝟏 : V)) ^* wm) := by
  have hes : ∀ e ∈ ([wm, wt, wone, wwp, ww, wtwo, wvp, wv, wu] : List V), IsSemiterm LAct 0 e := (List.forall_mem_cons.mpr ⟨hwm, List.forall_mem_cons.mpr ⟨hwt, List.forall_mem_cons.mpr ⟨hwone, List.forall_mem_cons.mpr ⟨hwwp, List.forall_mem_cons.mpr ⟨hww, List.forall_mem_cons.mpr ⟨hwtwo, List.forall_mem_cons.mpr ⟨hwvp, List.forall_mem_cons.mpr ⟨hwv, List.forall_mem_cons.mpr ⟨hwu, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩)
  unfold row_binNumeralEvenCert_as row_binNumeralEvenCert_c
  simp only [List.map_cons, List.map_nil]
  rw [instOuter_subst_listToVec _ isSemiformula_Ple (by rfl) _ hes (by row_entriesB), instOuter_subst_listToVec _ isSemiformula_Pbnum (by rfl) _ hes (by row_entriesB), instOuter_subst_listToVec _ isSemiformula_Pfunc (by rfl) _ hes (by row_entriesB), instOuter_subst_listToVec _ isSemiformula_Padjoin (by rfl) _ hes (by row_entriesB), instOuter_subst_listToVec _ isSemiformula_Padjoin (by rfl) _ hes (by row_entriesB), instOuter_subst_listToVec _ isSemiformula_Pfunc (by rfl) _ hes (by row_entriesB), instOuter_subst_listToVec _ isSemiformula_Padjoin (by rfl) _ hes (by row_entriesB), instOuter_subst_listToVec _ isSemiformula_Padjoin (by rfl) _ hes (by row_entriesB), instOuter_subst_listToVec _ isSemiformula_Pfunc (by rfl) _ hes (by row_entriesB), instOuter_subst_listToVec _ isSemiformula_Pbnum (by rfl) _ hes (by row_entriesB)]
  all_goals try row_entries_simpB
  row_finish

/-! ### `binNumeralOddCert` — `“u x x' s v v' two w w' one t m. …”`, `m = 12` -/

noncomputable def row_binNumeralOddCert_as : List V := [subst LAct (listToVec [(𝟏 : V), bv 11]) Ple, subst LAct (listToVec [bv 10, bv 11]) Pbnum, subst LAct (listToVec [bv 9, (𝟎 : V), cT 1, (𝟎 : V)]) Pfunc, subst LAct (listToVec [bv 8, bv 9, (𝟎 : V)]) Padjoin, subst LAct (listToVec [bv 7, bv 9, bv 8]) Padjoin, subst LAct (listToVec [bv 6, cT 2, (𝟎 : V), bv 7]) Pfunc, subst LAct (listToVec [bv 5, bv 10, (𝟎 : V)]) Padjoin, subst LAct (listToVec [bv 4, bv 6, bv 5]) Padjoin, subst LAct (listToVec [bv 3, cT 2, cT 1, bv 4]) Pfunc, subst LAct (listToVec [bv 2, bv 9, (𝟎 : V)]) Padjoin, subst LAct (listToVec [bv 1, bv 3, bv 2]) Padjoin, subst LAct (listToVec [bv 0, cT 2, (𝟎 : V), bv 1]) Pfunc]
noncomputable def row_binNumeralOddCert_c : V := subst LAct (listToVec [bv 0, ((((𝟏 : V) ^+ (𝟏 : V)) ^* bv 11) ^+ (𝟏 : V))]) Pbnum

theorem quote_row_binNumeralOddCert : (⌜Semiformula.lMap emb binNumeralOddCertB⌝ : V) = impChain LAct row_binNumeralOddCert_as row_binNumeralOddCert_c := by
  unfold binNumeralOddCertB row_binNumeralOddCert_as row_binNumeralOddCert_c Padjoin Pbnum Pfunc Ple leS
  all_goals row_shapeB

/-! ## G. Lengths: `termLenVec`/`listSum` bottom-up, the atom lengths with universal `M, s` (§3.6) -/

/-! ### `termLenVecNil` — `“x. …”`, `m = 1` -/

noncomputable def row_termLenVecNil_as : List V := []
noncomputable def row_termLenVecNil_c : V := subst LAct (listToVec [(𝟎 : V), (𝟎 : V), (𝟎 : V)]) PtlvG

theorem quote_row_termLenVecNil : (⌜Semiformula.lMap emb termLenVecNilB⌝ : V) = impChain LAct row_termLenVecNil_as row_termLenVecNil_c := by
  unfold termLenVecNilB row_termLenVecNil_as row_termLenVecNil_c PtlvG
  all_goals row_shapeB

lemma isSemiformula_termLenVecNil_c : IsSemiformula LAct ((1 : ℕ) : V) row_termLenVecNil_c := by
  unfold row_termLenVecNil_c
  exact isSemiformula_substRow isSemiformula_PtlvG _ (by rfl) (by row_entriesB)

/-- `termLenVecNil` at the witnesses `[wx]` (the DSL variables right-to-left). -/
lemma inst_termLenVecNil {wx : V} (hwx : IsSemiterm LAct 0 wx) :
    row_termLenVecNil_as.map (instOuter LAct [wx]) = [] ∧
    instOuter LAct [wx] row_termLenVecNil_c = tlvFact (𝟎 : V) (𝟎 : V) (𝟎 : V) := by
  have hes : ∀ e ∈ ([wx] : List V), IsSemiterm LAct 0 e := (List.forall_mem_cons.mpr ⟨hwx, List.forall_mem_nil _⟩)
  unfold row_termLenVecNil_as row_termLenVecNil_c
  simp only [List.map_cons, List.map_nil]
  rw [instOuter_subst_listToVec _ isSemiformula_PtlvG (by rfl) _ hes (by row_entriesB)]
  all_goals try row_entries_simpB
  row_finish

/-! ### `termLenVecAdj` — `“M' M l t v' v k n. …”`, `m = 8` -/

noncomputable def row_termLenVecAdj_as : List V := [subst LAct (listToVec [bv 7, bv 3]) PtPi, subst LAct (listToVec [bv 6, bv 5]) PutvPi, subst LAct (listToVec [bv 2, bv 3]) PtlenG, subst LAct (listToVec [bv 1, bv 6, bv 5]) PtlvG, subst LAct (listToVec [bv 4, bv 3, bv 5]) Padjoin, subst LAct (listToVec [bv 0, bv 2, bv 1]) Padjoin]
noncomputable def row_termLenVecAdj_c : V := subst LAct (listToVec [bv 0, (bv 6 ^+ (𝟏 : V)), bv 4]) PtlvG

theorem quote_row_termLenVecAdj : (⌜Semiformula.lMap emb termLenVecAdjB⌝ : V) = impChain LAct row_termLenVecAdj_as row_termLenVecAdj_c := by
  unfold termLenVecAdjB row_termLenVecAdj_as row_termLenVecAdj_c Padjoin PtPi PtlenG PtlvG PutvPi
  all_goals row_shapeB

lemma isSemiformula_termLenVecAdj_c : IsSemiformula LAct ((8 : ℕ) : V) row_termLenVecAdj_c := by
  unfold row_termLenVecAdj_c
  exact isSemiformula_substRow isSemiformula_PtlvG _ (by rfl) (by row_entriesB)

/-- `termLenVecAdj` at the witnesses `[wn, wk, wv, wvp, wt, wl, wM, wMp]` (the DSL variables right-to-left). -/
lemma inst_termLenVecAdj {wn wk wv wvp wt wl wM wMp : V} (hwn : IsSemiterm LAct 0 wn) (hwk : IsSemiterm LAct 0 wk) (hwv : IsSemiterm LAct 0 wv) (hwvp : IsSemiterm LAct 0 wvp) (hwt : IsSemiterm LAct 0 wt) (hwl : IsSemiterm LAct 0 wl) (hwM : IsSemiterm LAct 0 wM) (hwMp : IsSemiterm LAct 0 wMp) :
    row_termLenVecAdj_as.map (instOuter LAct [wn, wk, wv, wvp, wt, wl, wM, wMp]) = [tPiFact wn wt, utvPiFact wk wv, termLenMetaFact wl wt, tlvFact wM wk wv, adjFact wvp wt wv, adjFact wMp wl wM] ∧
    instOuter LAct [wn, wk, wv, wvp, wt, wl, wM, wMp] row_termLenVecAdj_c = tlvFact wMp (wk ^+ (𝟏 : V)) wvp := by
  have hes : ∀ e ∈ ([wn, wk, wv, wvp, wt, wl, wM, wMp] : List V), IsSemiterm LAct 0 e := (List.forall_mem_cons.mpr ⟨hwn, List.forall_mem_cons.mpr ⟨hwk, List.forall_mem_cons.mpr ⟨hwv, List.forall_mem_cons.mpr ⟨hwvp, List.forall_mem_cons.mpr ⟨hwt, List.forall_mem_cons.mpr ⟨hwl, List.forall_mem_cons.mpr ⟨hwM, List.forall_mem_cons.mpr ⟨hwMp, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩)
  unfold row_termLenVecAdj_as row_termLenVecAdj_c
  simp only [List.map_cons, List.map_nil]
  rw [instOuter_subst_listToVec _ isSemiformula_PtPi (by rfl) _ hes (by row_entriesB), instOuter_subst_listToVec _ isSemiformula_PutvPi (by rfl) _ hes (by row_entriesB), instOuter_subst_listToVec _ isSemiformula_PtlenG (by rfl) _ hes (by row_entriesB), instOuter_subst_listToVec _ isSemiformula_PtlvG (by rfl) _ hes (by row_entriesB), instOuter_subst_listToVec _ isSemiformula_Padjoin (by rfl) _ hes (by row_entriesB), instOuter_subst_listToVec _ isSemiformula_Padjoin (by rfl) _ hes (by row_entriesB), instOuter_subst_listToVec _ isSemiformula_PtlvG (by rfl) _ hes (by row_entriesB)]
  all_goals try row_entries_simpB
  row_finish

/-! ### `listSumNil` — `“x. …”`, `m = 1` -/

noncomputable def row_listSumNil_as : List V := []
noncomputable def row_listSumNil_c : V := subst LAct (listToVec [(𝟎 : V), (𝟎 : V)]) PlistSum

theorem quote_row_listSumNil : (⌜Semiformula.lMap emb listSumNilB⌝ : V) = impChain LAct row_listSumNil_as row_listSumNil_c := by
  unfold listSumNilB row_listSumNil_as row_listSumNil_c PlistSum
  all_goals row_shapeB

lemma isSemiformula_listSumNil_c : IsSemiformula LAct ((1 : ℕ) : V) row_listSumNil_c := by
  unfold row_listSumNil_c
  exact isSemiformula_substRow isSemiformula_PlistSum _ (by rfl) (by row_entriesB)

/-- `listSumNil` at the witnesses `[wx]` (the DSL variables right-to-left). -/
lemma inst_listSumNil {wx : V} (hwx : IsSemiterm LAct 0 wx) :
    row_listSumNil_as.map (instOuter LAct [wx]) = [] ∧
    instOuter LAct [wx] row_listSumNil_c = listSumFact (𝟎 : V) (𝟎 : V) := by
  have hes : ∀ e ∈ ([wx] : List V), IsSemiterm LAct 0 e := (List.forall_mem_cons.mpr ⟨hwx, List.forall_mem_nil _⟩)
  unfold row_listSumNil_as row_listSumNil_c
  simp only [List.map_cons, List.map_nil]
  rw [instOuter_subst_listToVec _ isSemiformula_PlistSum (by rfl) _ hes (by row_entriesB)]
  all_goals try row_entries_simpB
  row_finish

/-! ### `listSumAdj` — `“s' s l M M'. …”`, `m = 5` -/

noncomputable def row_listSumAdj_as : List V := [subst LAct (listToVec [bv 1, bv 3]) PlistSum, subst LAct (listToVec [bv 4, bv 2, bv 3]) Padjoin, subst LAct (listToVec [bv 0, bv 4]) PlistSum]
noncomputable def row_listSumAdj_c : V := subst LAct (listToVec [bv 0, (bv 2 ^+ bv 1)]) PeqB

/-! ### `formulaLenRelCert` — `“l s M p v R k. …”`, `m = 7` -/

noncomputable def row_formulaLenRelCert_as : List V := [subst LAct (listToVec [bv 6, bv 5]) PisRel, subst LAct (listToVec [bv 6, bv 4]) PutvPi, subst LAct (listToVec [bv 3, bv 6, bv 5, bv 4]) Prel, subst LAct (listToVec [bv 2, bv 6, bv 4]) PtlvG, subst LAct (listToVec [bv 1, bv 2]) PlistSum, subst LAct (listToVec [bv 0, bv 3]) PflenG]
noncomputable def row_formulaLenRelCert_c : V := subst LAct (listToVec [bv 0, (bv 1 ^+ (𝟏 : V))]) PeqB

theorem quote_row_formulaLenRelCert : (⌜Semiformula.lMap emb formulaLenRelCertB⌝ : V) = impChain LAct row_formulaLenRelCert_as row_formulaLenRelCert_c := by
  unfold formulaLenRelCertB row_formulaLenRelCert_as row_formulaLenRelCert_c PeqB PflenG PisRel PlistSum Prel PtlvG PutvPi
  all_goals row_shapeB

lemma isSemiformula_formulaLenRelCert_c : IsSemiformula LAct ((7 : ℕ) : V) row_formulaLenRelCert_c := by
  unfold row_formulaLenRelCert_c
  exact isSemiformula_substRow isSemiformula_PeqB _ (by rfl) (by row_entriesB)

/-- `formulaLenRelCert` at the witnesses `[wk, wR, wv, wp, wM, ws, wl]` (the DSL variables right-to-left). -/
lemma inst_formulaLenRelCert {wk wR wv wp wM ws wl : V} (hwk : IsSemiterm LAct 0 wk) (hwR : IsSemiterm LAct 0 wR) (hwv : IsSemiterm LAct 0 wv) (hwp : IsSemiterm LAct 0 wp) (hwM : IsSemiterm LAct 0 wM) (hws : IsSemiterm LAct 0 ws) (hwl : IsSemiterm LAct 0 wl) :
    row_formulaLenRelCert_as.map (instOuter LAct [wk, wR, wv, wp, wM, ws, wl]) = [isRelFact wk wR, utvPiFact wk wv, relFact wp wk wR wv, tlvFact wM wk wv, listSumFact ws wM, lenFact wl wp] ∧
    instOuter LAct [wk, wR, wv, wp, wM, ws, wl] row_formulaLenRelCert_c = eqFactB wl (ws ^+ (𝟏 : V)) := by
  have hes : ∀ e ∈ ([wk, wR, wv, wp, wM, ws, wl] : List V), IsSemiterm LAct 0 e := (List.forall_mem_cons.mpr ⟨hwk, List.forall_mem_cons.mpr ⟨hwR, List.forall_mem_cons.mpr ⟨hwv, List.forall_mem_cons.mpr ⟨hwp, List.forall_mem_cons.mpr ⟨hwM, List.forall_mem_cons.mpr ⟨hws, List.forall_mem_cons.mpr ⟨hwl, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩)
  unfold row_formulaLenRelCert_as row_formulaLenRelCert_c
  simp only [List.map_cons, List.map_nil]
  rw [instOuter_subst_listToVec _ isSemiformula_PisRel (by rfl) _ hes (by row_entriesB), instOuter_subst_listToVec _ isSemiformula_PutvPi (by rfl) _ hes (by row_entriesB), instOuter_subst_listToVec _ isSemiformula_Prel (by rfl) _ hes (by row_entriesB), instOuter_subst_listToVec _ isSemiformula_PtlvG (by rfl) _ hes (by row_entriesB), instOuter_subst_listToVec _ isSemiformula_PlistSum (by rfl) _ hes (by row_entriesB), instOuter_subst_listToVec _ isSemiformula_PflenG (by rfl) _ hes (by row_entriesB), instOuter_subst_listToVec _ isSemiformula_PeqB (by rfl) _ hes (by row_entriesB)]
  all_goals try row_entries_simpB
  row_finish

/-! ### `formulaLenNRelCert` — `“l s M p v R k. …”`, `m = 7` -/

noncomputable def row_formulaLenNRelCert_as : List V := [subst LAct (listToVec [bv 6, bv 5]) PisRel, subst LAct (listToVec [bv 6, bv 4]) PutvPi, subst LAct (listToVec [bv 3, bv 6, bv 5, bv 4]) Pnrel, subst LAct (listToVec [bv 2, bv 6, bv 4]) PtlvG, subst LAct (listToVec [bv 1, bv 2]) PlistSum, subst LAct (listToVec [bv 0, bv 3]) PflenG]
noncomputable def row_formulaLenNRelCert_c : V := subst LAct (listToVec [bv 0, (bv 1 ^+ (𝟏 : V))]) PeqB

theorem quote_row_formulaLenNRelCert : (⌜Semiformula.lMap emb formulaLenNRelCertB⌝ : V) = impChain LAct row_formulaLenNRelCert_as row_formulaLenNRelCert_c := by
  unfold formulaLenNRelCertB row_formulaLenNRelCert_as row_formulaLenNRelCert_c PeqB PflenG PisRel PlistSum Pnrel PtlvG PutvPi
  all_goals row_shapeB

lemma isSemiformula_formulaLenNRelCert_c : IsSemiformula LAct ((7 : ℕ) : V) row_formulaLenNRelCert_c := by
  unfold row_formulaLenNRelCert_c
  exact isSemiformula_substRow isSemiformula_PeqB _ (by rfl) (by row_entriesB)

/-- `formulaLenNRelCert` at the witnesses `[wk, wR, wv, wp, wM, ws, wl]` (the DSL variables right-to-left). -/
lemma inst_formulaLenNRelCert {wk wR wv wp wM ws wl : V} (hwk : IsSemiterm LAct 0 wk) (hwR : IsSemiterm LAct 0 wR) (hwv : IsSemiterm LAct 0 wv) (hwp : IsSemiterm LAct 0 wp) (hwM : IsSemiterm LAct 0 wM) (hws : IsSemiterm LAct 0 ws) (hwl : IsSemiterm LAct 0 wl) :
    row_formulaLenNRelCert_as.map (instOuter LAct [wk, wR, wv, wp, wM, ws, wl]) = [isRelFact wk wR, utvPiFact wk wv, nrelFact wp wk wR wv, tlvFact wM wk wv, listSumFact ws wM, lenFact wl wp] ∧
    instOuter LAct [wk, wR, wv, wp, wM, ws, wl] row_formulaLenNRelCert_c = eqFactB wl (ws ^+ (𝟏 : V)) := by
  have hes : ∀ e ∈ ([wk, wR, wv, wp, wM, ws, wl] : List V), IsSemiterm LAct 0 e := (List.forall_mem_cons.mpr ⟨hwk, List.forall_mem_cons.mpr ⟨hwR, List.forall_mem_cons.mpr ⟨hwv, List.forall_mem_cons.mpr ⟨hwp, List.forall_mem_cons.mpr ⟨hwM, List.forall_mem_cons.mpr ⟨hws, List.forall_mem_cons.mpr ⟨hwl, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩)
  unfold row_formulaLenNRelCert_as row_formulaLenNRelCert_c
  simp only [List.map_cons, List.map_nil]
  rw [instOuter_subst_listToVec _ isSemiformula_PisRel (by rfl) _ hes (by row_entriesB), instOuter_subst_listToVec _ isSemiformula_PutvPi (by rfl) _ hes (by row_entriesB), instOuter_subst_listToVec _ isSemiformula_Pnrel (by rfl) _ hes (by row_entriesB), instOuter_subst_listToVec _ isSemiformula_PtlvG (by rfl) _ hes (by row_entriesB), instOuter_subst_listToVec _ isSemiformula_PlistSum (by rfl) _ hes (by row_entriesB), instOuter_subst_listToVec _ isSemiformula_PflenG (by rfl) _ hes (by row_entriesB), instOuter_subst_listToVec _ isSemiformula_PeqB (by rfl) _ hes (by row_entriesB)]
  all_goals try row_entries_simpB
  row_finish

/-! ### `termLenFuncCert` — `“l s M t v f k. …”`, `m = 7` -/

noncomputable def row_termLenFuncCert_as : List V := [subst LAct (listToVec [bv 6, bv 5]) PisFunc, subst LAct (listToVec [bv 6, bv 4]) PutvPi, subst LAct (listToVec [bv 3, bv 6, bv 5, bv 4]) Pfunc, subst LAct (listToVec [bv 2, bv 6, bv 4]) PtlvG, subst LAct (listToVec [bv 1, bv 2]) PlistSum, subst LAct (listToVec [bv 0, bv 3]) PtlenG]
noncomputable def row_termLenFuncCert_c : V := subst LAct (listToVec [bv 0, (bv 1 ^+ (𝟏 : V))]) PeqB

theorem quote_row_termLenFuncCert : (⌜Semiformula.lMap emb termLenFuncCertB⌝ : V) = impChain LAct row_termLenFuncCert_as row_termLenFuncCert_c := by
  unfold termLenFuncCertB row_termLenFuncCert_as row_termLenFuncCert_c PeqB Pfunc PisFunc PlistSum PtlenG PtlvG PutvPi
  all_goals row_shapeB

lemma isSemiformula_termLenFuncCert_c : IsSemiformula LAct ((7 : ℕ) : V) row_termLenFuncCert_c := by
  unfold row_termLenFuncCert_c
  exact isSemiformula_substRow isSemiformula_PeqB _ (by rfl) (by row_entriesB)

/-- `termLenFuncCert` at the witnesses `[wk, wf, wv, wt, wM, ws, wl]` (the DSL variables right-to-left). -/
lemma inst_termLenFuncCert {wk wf wv wt wM ws wl : V} (hwk : IsSemiterm LAct 0 wk) (hwf : IsSemiterm LAct 0 wf) (hwv : IsSemiterm LAct 0 wv) (hwt : IsSemiterm LAct 0 wt) (hwM : IsSemiterm LAct 0 wM) (hws : IsSemiterm LAct 0 ws) (hwl : IsSemiterm LAct 0 wl) :
    row_termLenFuncCert_as.map (instOuter LAct [wk, wf, wv, wt, wM, ws, wl]) = [isFuncFact wk wf, utvPiFact wk wv, funcFact wt wk wf wv, tlvFact wM wk wv, listSumFact ws wM, termLenMetaFact wl wt] ∧
    instOuter LAct [wk, wf, wv, wt, wM, ws, wl] row_termLenFuncCert_c = eqFactB wl (ws ^+ (𝟏 : V)) := by
  have hes : ∀ e ∈ ([wk, wf, wv, wt, wM, ws, wl] : List V), IsSemiterm LAct 0 e := (List.forall_mem_cons.mpr ⟨hwk, List.forall_mem_cons.mpr ⟨hwf, List.forall_mem_cons.mpr ⟨hwv, List.forall_mem_cons.mpr ⟨hwt, List.forall_mem_cons.mpr ⟨hwM, List.forall_mem_cons.mpr ⟨hws, List.forall_mem_cons.mpr ⟨hwl, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩)
  unfold row_termLenFuncCert_as row_termLenFuncCert_c
  simp only [List.map_cons, List.map_nil]
  rw [instOuter_subst_listToVec _ isSemiformula_PisFunc (by rfl) _ hes (by row_entriesB), instOuter_subst_listToVec _ isSemiformula_PutvPi (by rfl) _ hes (by row_entriesB), instOuter_subst_listToVec _ isSemiformula_Pfunc (by rfl) _ hes (by row_entriesB), instOuter_subst_listToVec _ isSemiformula_PtlvG (by rfl) _ hes (by row_entriesB), instOuter_subst_listToVec _ isSemiformula_PlistSum (by rfl) _ hes (by row_entriesB), instOuter_subst_listToVec _ isSemiformula_PtlenG (by rfl) _ hes (by row_entriesB), instOuter_subst_listToVec _ isSemiformula_PeqB (by rfl) _ hes (by row_entriesB)]
  all_goals try row_entries_simpB
  row_finish

/-! ## H. Certification: `neg`/`shift`/`subst`/`free` bottom-up, the term level, `qVec` (§3.6) -/

/-! ### `negRelCert` — `“y v R k r. …”`, `m = 5` -/

noncomputable def row_negRelCert_as : List V := [subst LAct (listToVec [bv 3, bv 2]) PisRel, subst LAct (listToVec [bv 3, bv 1]) PutvPi, subst LAct (listToVec [bv 4, bv 3, bv 2, bv 1]) Prel, subst LAct (listToVec [bv 0, bv 3, bv 2, bv 1]) Pnrel]
noncomputable def row_negRelCert_c : V := subst LAct (listToVec [bv 0, bv 4]) PnegG

theorem quote_row_negRelCert : (⌜Semiformula.lMap emb negRelCertB⌝ : V) = impChain LAct row_negRelCert_as row_negRelCert_c := by
  unfold negRelCertB row_negRelCert_as row_negRelCert_c PisRel PnegG Pnrel Prel PutvPi
  all_goals row_shapeB

lemma isSemiformula_negRelCert_c : IsSemiformula LAct ((5 : ℕ) : V) row_negRelCert_c := by
  unfold row_negRelCert_c
  exact isSemiformula_substRow isSemiformula_PnegG _ (by rfl) (by row_entriesB)

/-- `negRelCert` at the witnesses `[wr, wk, wR, wv, wy]` (the DSL variables right-to-left). -/
lemma inst_negRelCert {wr wk wR wv wy : V} (hwr : IsSemiterm LAct 0 wr) (hwk : IsSemiterm LAct 0 wk) (hwR : IsSemiterm LAct 0 wR) (hwv : IsSemiterm LAct 0 wv) (hwy : IsSemiterm LAct 0 wy) :
    row_negRelCert_as.map (instOuter LAct [wr, wk, wR, wv, wy]) = [isRelFact wk wR, utvPiFact wk wv, relFact wr wk wR wv, nrelFact wy wk wR wv] ∧
    instOuter LAct [wr, wk, wR, wv, wy] row_negRelCert_c = negFact wy wr := by
  have hes : ∀ e ∈ ([wr, wk, wR, wv, wy] : List V), IsSemiterm LAct 0 e := (List.forall_mem_cons.mpr ⟨hwr, List.forall_mem_cons.mpr ⟨hwk, List.forall_mem_cons.mpr ⟨hwR, List.forall_mem_cons.mpr ⟨hwv, List.forall_mem_cons.mpr ⟨hwy, List.forall_mem_nil _⟩⟩⟩⟩⟩)
  unfold row_negRelCert_as row_negRelCert_c
  simp only [List.map_cons, List.map_nil]
  rw [instOuter_subst_listToVec _ isSemiformula_PisRel (by rfl) _ hes (by row_entriesB), instOuter_subst_listToVec _ isSemiformula_PutvPi (by rfl) _ hes (by row_entriesB), instOuter_subst_listToVec _ isSemiformula_Prel (by rfl) _ hes (by row_entriesB), instOuter_subst_listToVec _ isSemiformula_Pnrel (by rfl) _ hes (by row_entriesB), instOuter_subst_listToVec _ isSemiformula_PnegG (by rfl) _ hes (by row_entriesB)]
  all_goals try row_entries_simpB
  row_finish

/-! ### `negNRelCert` — `“y v R k r. …”`, `m = 5` -/

noncomputable def row_negNRelCert_as : List V := [subst LAct (listToVec [bv 3, bv 2]) PisRel, subst LAct (listToVec [bv 3, bv 1]) PutvPi, subst LAct (listToVec [bv 4, bv 3, bv 2, bv 1]) Pnrel, subst LAct (listToVec [bv 0, bv 3, bv 2, bv 1]) Prel]
noncomputable def row_negNRelCert_c : V := subst LAct (listToVec [bv 0, bv 4]) PnegG

theorem quote_row_negNRelCert : (⌜Semiformula.lMap emb negNRelCertB⌝ : V) = impChain LAct row_negNRelCert_as row_negNRelCert_c := by
  unfold negNRelCertB row_negNRelCert_as row_negNRelCert_c PisRel PnegG Pnrel Prel PutvPi
  all_goals row_shapeB

lemma isSemiformula_negNRelCert_c : IsSemiformula LAct ((5 : ℕ) : V) row_negNRelCert_c := by
  unfold row_negNRelCert_c
  exact isSemiformula_substRow isSemiformula_PnegG _ (by rfl) (by row_entriesB)

/-- `negNRelCert` at the witnesses `[wr, wk, wR, wv, wy]` (the DSL variables right-to-left). -/
lemma inst_negNRelCert {wr wk wR wv wy : V} (hwr : IsSemiterm LAct 0 wr) (hwk : IsSemiterm LAct 0 wk) (hwR : IsSemiterm LAct 0 wR) (hwv : IsSemiterm LAct 0 wv) (hwy : IsSemiterm LAct 0 wy) :
    row_negNRelCert_as.map (instOuter LAct [wr, wk, wR, wv, wy]) = [isRelFact wk wR, utvPiFact wk wv, nrelFact wr wk wR wv, relFact wy wk wR wv] ∧
    instOuter LAct [wr, wk, wR, wv, wy] row_negNRelCert_c = negFact wy wr := by
  have hes : ∀ e ∈ ([wr, wk, wR, wv, wy] : List V), IsSemiterm LAct 0 e := (List.forall_mem_cons.mpr ⟨hwr, List.forall_mem_cons.mpr ⟨hwk, List.forall_mem_cons.mpr ⟨hwR, List.forall_mem_cons.mpr ⟨hwv, List.forall_mem_cons.mpr ⟨hwy, List.forall_mem_nil _⟩⟩⟩⟩⟩)
  unfold row_negNRelCert_as row_negNRelCert_c
  simp only [List.map_cons, List.map_nil]
  rw [instOuter_subst_listToVec _ isSemiformula_PisRel (by rfl) _ hes (by row_entriesB), instOuter_subst_listToVec _ isSemiformula_PutvPi (by rfl) _ hes (by row_entriesB), instOuter_subst_listToVec _ isSemiformula_Pnrel (by rfl) _ hes (by row_entriesB), instOuter_subst_listToVec _ isSemiformula_Prel (by rfl) _ hes (by row_entriesB), instOuter_subst_listToVec _ isSemiformula_PnegG (by rfl) _ hes (by row_entriesB)]
  all_goals try row_entries_simpB
  row_finish

/-! ### `negVerumCert` — `“y r. …”`, `m = 2` -/

noncomputable def row_negVerumCert_as : List V := [subst LAct (listToVec [bv 1]) Pverum, subst LAct (listToVec [bv 0]) Pfalsum]
noncomputable def row_negVerumCert_c : V := subst LAct (listToVec [bv 0, bv 1]) PnegG

theorem quote_row_negVerumCert : (⌜Semiformula.lMap emb negVerumCertB⌝ : V) = impChain LAct row_negVerumCert_as row_negVerumCert_c := by
  unfold negVerumCertB row_negVerumCert_as row_negVerumCert_c Pfalsum PnegG Pverum
  all_goals row_shapeB

lemma isSemiformula_negVerumCert_c : IsSemiformula LAct ((2 : ℕ) : V) row_negVerumCert_c := by
  unfold row_negVerumCert_c
  exact isSemiformula_substRow isSemiformula_PnegG _ (by rfl) (by row_entriesB)

/-- `negVerumCert` at the witnesses `[wr, wy]` (the DSL variables right-to-left). -/
lemma inst_negVerumCert {wr wy : V} (hwr : IsSemiterm LAct 0 wr) (hwy : IsSemiterm LAct 0 wy) :
    row_negVerumCert_as.map (instOuter LAct [wr, wy]) = [verumFact wr, falsumFact wy] ∧
    instOuter LAct [wr, wy] row_negVerumCert_c = negFact wy wr := by
  have hes : ∀ e ∈ ([wr, wy] : List V), IsSemiterm LAct 0 e := (List.forall_mem_cons.mpr ⟨hwr, List.forall_mem_cons.mpr ⟨hwy, List.forall_mem_nil _⟩⟩)
  unfold row_negVerumCert_as row_negVerumCert_c
  simp only [List.map_cons, List.map_nil]
  rw [instOuter_subst_listToVec _ isSemiformula_Pverum (by rfl) _ hes (by row_entriesB), instOuter_subst_listToVec _ isSemiformula_Pfalsum (by rfl) _ hes (by row_entriesB), instOuter_subst_listToVec _ isSemiformula_PnegG (by rfl) _ hes (by row_entriesB)]
  all_goals try row_entries_simpB
  row_finish

/-! ### `negFalsumCert` — `“y r. …”`, `m = 2` -/

noncomputable def row_negFalsumCert_as : List V := [subst LAct (listToVec [bv 1]) Pfalsum, subst LAct (listToVec [bv 0]) Pverum]
noncomputable def row_negFalsumCert_c : V := subst LAct (listToVec [bv 0, bv 1]) PnegG

theorem quote_row_negFalsumCert : (⌜Semiformula.lMap emb negFalsumCertB⌝ : V) = impChain LAct row_negFalsumCert_as row_negFalsumCert_c := by
  unfold negFalsumCertB row_negFalsumCert_as row_negFalsumCert_c Pfalsum PnegG Pverum
  all_goals row_shapeB

lemma isSemiformula_negFalsumCert_c : IsSemiformula LAct ((2 : ℕ) : V) row_negFalsumCert_c := by
  unfold row_negFalsumCert_c
  exact isSemiformula_substRow isSemiformula_PnegG _ (by rfl) (by row_entriesB)

/-- `negFalsumCert` at the witnesses `[wr, wy]` (the DSL variables right-to-left). -/
lemma inst_negFalsumCert {wr wy : V} (hwr : IsSemiterm LAct 0 wr) (hwy : IsSemiterm LAct 0 wy) :
    row_negFalsumCert_as.map (instOuter LAct [wr, wy]) = [falsumFact wr, verumFact wy] ∧
    instOuter LAct [wr, wy] row_negFalsumCert_c = negFact wy wr := by
  have hes : ∀ e ∈ ([wr, wy] : List V), IsSemiterm LAct 0 e := (List.forall_mem_cons.mpr ⟨hwr, List.forall_mem_cons.mpr ⟨hwy, List.forall_mem_nil _⟩⟩)
  unfold row_negFalsumCert_as row_negFalsumCert_c
  simp only [List.map_cons, List.map_nil]
  rw [instOuter_subst_listToVec _ isSemiformula_Pfalsum (by rfl) _ hes (by row_entriesB), instOuter_subst_listToVec _ isSemiformula_Pverum (by rfl) _ hes (by row_entriesB), instOuter_subst_listToVec _ isSemiformula_PnegG (by rfl) _ hes (by row_entriesB)]
  all_goals try row_entries_simpB
  row_finish

/-! ### `negAndCert` — `“y nq np r q p n. …”`, `m = 7` -/

noncomputable def row_negAndCert_as : List V := [subst LAct (listToVec [bv 6, bv 5]) Ppi, subst LAct (listToVec [bv 6, bv 4]) Ppi, subst LAct (listToVec [bv 3, bv 5, bv 4]) Pand, subst LAct (listToVec [bv 2, bv 5]) PnegG, subst LAct (listToVec [bv 1, bv 4]) PnegG, subst LAct (listToVec [bv 0, bv 2, bv 1]) Por]
noncomputable def row_negAndCert_c : V := subst LAct (listToVec [bv 0, bv 3]) PnegG

theorem quote_row_negAndCert : (⌜Semiformula.lMap emb negAndCertB⌝ : V) = impChain LAct row_negAndCert_as row_negAndCert_c := by
  unfold negAndCertB row_negAndCert_as row_negAndCert_c Pand PnegG Por Ppi
  all_goals row_shapeB

lemma isSemiformula_negAndCert_c : IsSemiformula LAct ((7 : ℕ) : V) row_negAndCert_c := by
  unfold row_negAndCert_c
  exact isSemiformula_substRow isSemiformula_PnegG _ (by rfl) (by row_entriesB)

/-- `negAndCert` at the witnesses `[wn, wp, wq, wr, wnp, wnq, wy]` (the DSL variables right-to-left). -/
lemma inst_negAndCert {wn wp wq wr wnp wnq wy : V} (hwn : IsSemiterm LAct 0 wn) (hwp : IsSemiterm LAct 0 wp) (hwq : IsSemiterm LAct 0 wq) (hwr : IsSemiterm LAct 0 wr) (hwnp : IsSemiterm LAct 0 wnp) (hwnq : IsSemiterm LAct 0 wnq) (hwy : IsSemiterm LAct 0 wy) :
    row_negAndCert_as.map (instOuter LAct [wn, wp, wq, wr, wnp, wnq, wy]) = [piFact wn wp, piFact wn wq, andFact wr wp wq, negFact wnp wp, negFact wnq wq, orFact wy wnp wnq] ∧
    instOuter LAct [wn, wp, wq, wr, wnp, wnq, wy] row_negAndCert_c = negFact wy wr := by
  have hes : ∀ e ∈ ([wn, wp, wq, wr, wnp, wnq, wy] : List V), IsSemiterm LAct 0 e := (List.forall_mem_cons.mpr ⟨hwn, List.forall_mem_cons.mpr ⟨hwp, List.forall_mem_cons.mpr ⟨hwq, List.forall_mem_cons.mpr ⟨hwr, List.forall_mem_cons.mpr ⟨hwnp, List.forall_mem_cons.mpr ⟨hwnq, List.forall_mem_cons.mpr ⟨hwy, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩)
  unfold row_negAndCert_as row_negAndCert_c
  simp only [List.map_cons, List.map_nil]
  rw [instOuter_subst_listToVec _ isSemiformula_Ppi (by rfl) _ hes (by row_entriesB), instOuter_subst_listToVec _ isSemiformula_Ppi (by rfl) _ hes (by row_entriesB), instOuter_subst_listToVec _ isSemiformula_Pand (by rfl) _ hes (by row_entriesB), instOuter_subst_listToVec _ isSemiformula_PnegG (by rfl) _ hes (by row_entriesB), instOuter_subst_listToVec _ isSemiformula_PnegG (by rfl) _ hes (by row_entriesB), instOuter_subst_listToVec _ isSemiformula_Por (by rfl) _ hes (by row_entriesB), instOuter_subst_listToVec _ isSemiformula_PnegG (by rfl) _ hes (by row_entriesB)]
  all_goals try row_entries_simpB
  row_finish

/-! ### `negOrCert` — `“y nq np r q p n. …”`, `m = 7` -/

noncomputable def row_negOrCert_as : List V := [subst LAct (listToVec [bv 6, bv 5]) Ppi, subst LAct (listToVec [bv 6, bv 4]) Ppi, subst LAct (listToVec [bv 3, bv 5, bv 4]) Por, subst LAct (listToVec [bv 2, bv 5]) PnegG, subst LAct (listToVec [bv 1, bv 4]) PnegG, subst LAct (listToVec [bv 0, bv 2, bv 1]) Pand]
noncomputable def row_negOrCert_c : V := subst LAct (listToVec [bv 0, bv 3]) PnegG

theorem quote_row_negOrCert : (⌜Semiformula.lMap emb negOrCertB⌝ : V) = impChain LAct row_negOrCert_as row_negOrCert_c := by
  unfold negOrCertB row_negOrCert_as row_negOrCert_c Pand PnegG Por Ppi
  all_goals row_shapeB

lemma isSemiformula_negOrCert_c : IsSemiformula LAct ((7 : ℕ) : V) row_negOrCert_c := by
  unfold row_negOrCert_c
  exact isSemiformula_substRow isSemiformula_PnegG _ (by rfl) (by row_entriesB)

/-- `negOrCert` at the witnesses `[wn, wp, wq, wr, wnp, wnq, wy]` (the DSL variables right-to-left). -/
lemma inst_negOrCert {wn wp wq wr wnp wnq wy : V} (hwn : IsSemiterm LAct 0 wn) (hwp : IsSemiterm LAct 0 wp) (hwq : IsSemiterm LAct 0 wq) (hwr : IsSemiterm LAct 0 wr) (hwnp : IsSemiterm LAct 0 wnp) (hwnq : IsSemiterm LAct 0 wnq) (hwy : IsSemiterm LAct 0 wy) :
    row_negOrCert_as.map (instOuter LAct [wn, wp, wq, wr, wnp, wnq, wy]) = [piFact wn wp, piFact wn wq, orFact wr wp wq, negFact wnp wp, negFact wnq wq, andFact wy wnp wnq] ∧
    instOuter LAct [wn, wp, wq, wr, wnp, wnq, wy] row_negOrCert_c = negFact wy wr := by
  have hes : ∀ e ∈ ([wn, wp, wq, wr, wnp, wnq, wy] : List V), IsSemiterm LAct 0 e := (List.forall_mem_cons.mpr ⟨hwn, List.forall_mem_cons.mpr ⟨hwp, List.forall_mem_cons.mpr ⟨hwq, List.forall_mem_cons.mpr ⟨hwr, List.forall_mem_cons.mpr ⟨hwnp, List.forall_mem_cons.mpr ⟨hwnq, List.forall_mem_cons.mpr ⟨hwy, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩)
  unfold row_negOrCert_as row_negOrCert_c
  simp only [List.map_cons, List.map_nil]
  rw [instOuter_subst_listToVec _ isSemiformula_Ppi (by rfl) _ hes (by row_entriesB), instOuter_subst_listToVec _ isSemiformula_Ppi (by rfl) _ hes (by row_entriesB), instOuter_subst_listToVec _ isSemiformula_Por (by rfl) _ hes (by row_entriesB), instOuter_subst_listToVec _ isSemiformula_PnegG (by rfl) _ hes (by row_entriesB), instOuter_subst_listToVec _ isSemiformula_PnegG (by rfl) _ hes (by row_entriesB), instOuter_subst_listToVec _ isSemiformula_Pand (by rfl) _ hes (by row_entriesB), instOuter_subst_listToVec _ isSemiformula_PnegG (by rfl) _ hes (by row_entriesB)]
  all_goals try row_entries_simpB
  row_finish

/-! ### `negAllCert` — `“y np r p n. …”`, `m = 5` -/

noncomputable def row_negAllCert_as : List V := [subst LAct (listToVec [(bv 4 ^+ (𝟏 : V)), bv 3]) Ppi, subst LAct (listToVec [bv 2, bv 3]) Pall, subst LAct (listToVec [bv 1, bv 3]) PnegG, subst LAct (listToVec [bv 0, bv 1]) Pexs]
noncomputable def row_negAllCert_c : V := subst LAct (listToVec [bv 0, bv 2]) PnegG

theorem quote_row_negAllCert : (⌜Semiformula.lMap emb negAllCertB⌝ : V) = impChain LAct row_negAllCert_as row_negAllCert_c := by
  unfold negAllCertB row_negAllCert_as row_negAllCert_c Pall Pexs PnegG Ppi
  all_goals row_shapeB

lemma isSemiformula_negAllCert_c : IsSemiformula LAct ((5 : ℕ) : V) row_negAllCert_c := by
  unfold row_negAllCert_c
  exact isSemiformula_substRow isSemiformula_PnegG _ (by rfl) (by row_entriesB)

/-- `negAllCert` at the witnesses `[wn, wp, wr, wnp, wy]` (the DSL variables right-to-left). -/
lemma inst_negAllCert {wn wp wr wnp wy : V} (hwn : IsSemiterm LAct 0 wn) (hwp : IsSemiterm LAct 0 wp) (hwr : IsSemiterm LAct 0 wr) (hwnp : IsSemiterm LAct 0 wnp) (hwy : IsSemiterm LAct 0 wy) :
    row_negAllCert_as.map (instOuter LAct [wn, wp, wr, wnp, wy]) = [piFact (wn ^+ (𝟏 : V)) wp, allFact wr wp, negFact wnp wp, exsFact wy wnp] ∧
    instOuter LAct [wn, wp, wr, wnp, wy] row_negAllCert_c = negFact wy wr := by
  have hes : ∀ e ∈ ([wn, wp, wr, wnp, wy] : List V), IsSemiterm LAct 0 e := (List.forall_mem_cons.mpr ⟨hwn, List.forall_mem_cons.mpr ⟨hwp, List.forall_mem_cons.mpr ⟨hwr, List.forall_mem_cons.mpr ⟨hwnp, List.forall_mem_cons.mpr ⟨hwy, List.forall_mem_nil _⟩⟩⟩⟩⟩)
  unfold row_negAllCert_as row_negAllCert_c
  simp only [List.map_cons, List.map_nil]
  rw [instOuter_subst_listToVec _ isSemiformula_Ppi (by rfl) _ hes (by row_entriesB), instOuter_subst_listToVec _ isSemiformula_Pall (by rfl) _ hes (by row_entriesB), instOuter_subst_listToVec _ isSemiformula_PnegG (by rfl) _ hes (by row_entriesB), instOuter_subst_listToVec _ isSemiformula_Pexs (by rfl) _ hes (by row_entriesB), instOuter_subst_listToVec _ isSemiformula_PnegG (by rfl) _ hes (by row_entriesB)]
  all_goals try row_entries_simpB
  row_finish

/-! ### `negExsCert` — `“y np r p n. …”`, `m = 5` -/

noncomputable def row_negExsCert_as : List V := [subst LAct (listToVec [(bv 4 ^+ (𝟏 : V)), bv 3]) Ppi, subst LAct (listToVec [bv 2, bv 3]) Pexs, subst LAct (listToVec [bv 1, bv 3]) PnegG, subst LAct (listToVec [bv 0, bv 1]) Pall]
noncomputable def row_negExsCert_c : V := subst LAct (listToVec [bv 0, bv 2]) PnegG

theorem quote_row_negExsCert : (⌜Semiformula.lMap emb negExsCertB⌝ : V) = impChain LAct row_negExsCert_as row_negExsCert_c := by
  unfold negExsCertB row_negExsCert_as row_negExsCert_c Pall Pexs PnegG Ppi
  all_goals row_shapeB

lemma isSemiformula_negExsCert_c : IsSemiformula LAct ((5 : ℕ) : V) row_negExsCert_c := by
  unfold row_negExsCert_c
  exact isSemiformula_substRow isSemiformula_PnegG _ (by rfl) (by row_entriesB)

/-- `negExsCert` at the witnesses `[wn, wp, wr, wnp, wy]` (the DSL variables right-to-left). -/
lemma inst_negExsCert {wn wp wr wnp wy : V} (hwn : IsSemiterm LAct 0 wn) (hwp : IsSemiterm LAct 0 wp) (hwr : IsSemiterm LAct 0 wr) (hwnp : IsSemiterm LAct 0 wnp) (hwy : IsSemiterm LAct 0 wy) :
    row_negExsCert_as.map (instOuter LAct [wn, wp, wr, wnp, wy]) = [piFact (wn ^+ (𝟏 : V)) wp, exsFact wr wp, negFact wnp wp, allFact wy wnp] ∧
    instOuter LAct [wn, wp, wr, wnp, wy] row_negExsCert_c = negFact wy wr := by
  have hes : ∀ e ∈ ([wn, wp, wr, wnp, wy] : List V), IsSemiterm LAct 0 e := (List.forall_mem_cons.mpr ⟨hwn, List.forall_mem_cons.mpr ⟨hwp, List.forall_mem_cons.mpr ⟨hwr, List.forall_mem_cons.mpr ⟨hwnp, List.forall_mem_cons.mpr ⟨hwy, List.forall_mem_nil _⟩⟩⟩⟩⟩)
  unfold row_negExsCert_as row_negExsCert_c
  simp only [List.map_cons, List.map_nil]
  rw [instOuter_subst_listToVec _ isSemiformula_Ppi (by rfl) _ hes (by row_entriesB), instOuter_subst_listToVec _ isSemiformula_Pexs (by rfl) _ hes (by row_entriesB), instOuter_subst_listToVec _ isSemiformula_PnegG (by rfl) _ hes (by row_entriesB), instOuter_subst_listToVec _ isSemiformula_Pall (by rfl) _ hes (by row_entriesB), instOuter_subst_listToVec _ isSemiformula_PnegG (by rfl) _ hes (by row_entriesB)]
  all_goals try row_entries_simpB
  row_finish

/-! ### `shiftRelCert` — `“y u v R k r. …”`, `m = 6` -/

noncomputable def row_shiftRelCert_as : List V := [subst LAct (listToVec [bv 4, bv 3]) PisRel, subst LAct (listToVec [bv 4, bv 2]) PutvPi, subst LAct (listToVec [bv 5, bv 4, bv 3, bv 2]) Prel, subst LAct (listToVec [bv 1, bv 4, bv 2]) PtshvG, subst LAct (listToVec [bv 0, bv 4, bv 3, bv 1]) Prel]
noncomputable def row_shiftRelCert_c : V := subst LAct (listToVec [bv 0, bv 5]) PshiftG

theorem quote_row_shiftRelCert : (⌜Semiformula.lMap emb shiftRelCertB⌝ : V) = impChain LAct row_shiftRelCert_as row_shiftRelCert_c := by
  unfold shiftRelCertB row_shiftRelCert_as row_shiftRelCert_c PisRel Prel PshiftG PtshvG PutvPi
  all_goals row_shapeB

lemma isSemiformula_shiftRelCert_c : IsSemiformula LAct ((6 : ℕ) : V) row_shiftRelCert_c := by
  unfold row_shiftRelCert_c
  exact isSemiformula_substRow isSemiformula_PshiftG _ (by rfl) (by row_entriesB)

/-- `shiftRelCert` at the witnesses `[wr, wk, wR, wv, wu, wy]` (the DSL variables right-to-left). -/
lemma inst_shiftRelCert {wr wk wR wv wu wy : V} (hwr : IsSemiterm LAct 0 wr) (hwk : IsSemiterm LAct 0 wk) (hwR : IsSemiterm LAct 0 wR) (hwv : IsSemiterm LAct 0 wv) (hwu : IsSemiterm LAct 0 wu) (hwy : IsSemiterm LAct 0 wy) :
    row_shiftRelCert_as.map (instOuter LAct [wr, wk, wR, wv, wu, wy]) = [isRelFact wk wR, utvPiFact wk wv, relFact wr wk wR wv, tshvFact wu wk wv, relFact wy wk wR wu] ∧
    instOuter LAct [wr, wk, wR, wv, wu, wy] row_shiftRelCert_c = shiftFact wy wr := by
  have hes : ∀ e ∈ ([wr, wk, wR, wv, wu, wy] : List V), IsSemiterm LAct 0 e := (List.forall_mem_cons.mpr ⟨hwr, List.forall_mem_cons.mpr ⟨hwk, List.forall_mem_cons.mpr ⟨hwR, List.forall_mem_cons.mpr ⟨hwv, List.forall_mem_cons.mpr ⟨hwu, List.forall_mem_cons.mpr ⟨hwy, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩)
  unfold row_shiftRelCert_as row_shiftRelCert_c
  simp only [List.map_cons, List.map_nil]
  rw [instOuter_subst_listToVec _ isSemiformula_PisRel (by rfl) _ hes (by row_entriesB), instOuter_subst_listToVec _ isSemiformula_PutvPi (by rfl) _ hes (by row_entriesB), instOuter_subst_listToVec _ isSemiformula_Prel (by rfl) _ hes (by row_entriesB), instOuter_subst_listToVec _ isSemiformula_PtshvG (by rfl) _ hes (by row_entriesB), instOuter_subst_listToVec _ isSemiformula_Prel (by rfl) _ hes (by row_entriesB), instOuter_subst_listToVec _ isSemiformula_PshiftG (by rfl) _ hes (by row_entriesB)]
  all_goals try row_entries_simpB
  row_finish

/-! ### `shiftNRelCert` — `“y u v R k r. …”`, `m = 6` -/

noncomputable def row_shiftNRelCert_as : List V := [subst LAct (listToVec [bv 4, bv 3]) PisRel, subst LAct (listToVec [bv 4, bv 2]) PutvPi, subst LAct (listToVec [bv 5, bv 4, bv 3, bv 2]) Pnrel, subst LAct (listToVec [bv 1, bv 4, bv 2]) PtshvG, subst LAct (listToVec [bv 0, bv 4, bv 3, bv 1]) Pnrel]
noncomputable def row_shiftNRelCert_c : V := subst LAct (listToVec [bv 0, bv 5]) PshiftG

theorem quote_row_shiftNRelCert : (⌜Semiformula.lMap emb shiftNRelCertB⌝ : V) = impChain LAct row_shiftNRelCert_as row_shiftNRelCert_c := by
  unfold shiftNRelCertB row_shiftNRelCert_as row_shiftNRelCert_c PisRel Pnrel PshiftG PtshvG PutvPi
  all_goals row_shapeB

lemma isSemiformula_shiftNRelCert_c : IsSemiformula LAct ((6 : ℕ) : V) row_shiftNRelCert_c := by
  unfold row_shiftNRelCert_c
  exact isSemiformula_substRow isSemiformula_PshiftG _ (by rfl) (by row_entriesB)

/-- `shiftNRelCert` at the witnesses `[wr, wk, wR, wv, wu, wy]` (the DSL variables right-to-left). -/
lemma inst_shiftNRelCert {wr wk wR wv wu wy : V} (hwr : IsSemiterm LAct 0 wr) (hwk : IsSemiterm LAct 0 wk) (hwR : IsSemiterm LAct 0 wR) (hwv : IsSemiterm LAct 0 wv) (hwu : IsSemiterm LAct 0 wu) (hwy : IsSemiterm LAct 0 wy) :
    row_shiftNRelCert_as.map (instOuter LAct [wr, wk, wR, wv, wu, wy]) = [isRelFact wk wR, utvPiFact wk wv, nrelFact wr wk wR wv, tshvFact wu wk wv, nrelFact wy wk wR wu] ∧
    instOuter LAct [wr, wk, wR, wv, wu, wy] row_shiftNRelCert_c = shiftFact wy wr := by
  have hes : ∀ e ∈ ([wr, wk, wR, wv, wu, wy] : List V), IsSemiterm LAct 0 e := (List.forall_mem_cons.mpr ⟨hwr, List.forall_mem_cons.mpr ⟨hwk, List.forall_mem_cons.mpr ⟨hwR, List.forall_mem_cons.mpr ⟨hwv, List.forall_mem_cons.mpr ⟨hwu, List.forall_mem_cons.mpr ⟨hwy, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩)
  unfold row_shiftNRelCert_as row_shiftNRelCert_c
  simp only [List.map_cons, List.map_nil]
  rw [instOuter_subst_listToVec _ isSemiformula_PisRel (by rfl) _ hes (by row_entriesB), instOuter_subst_listToVec _ isSemiformula_PutvPi (by rfl) _ hes (by row_entriesB), instOuter_subst_listToVec _ isSemiformula_Pnrel (by rfl) _ hes (by row_entriesB), instOuter_subst_listToVec _ isSemiformula_PtshvG (by rfl) _ hes (by row_entriesB), instOuter_subst_listToVec _ isSemiformula_Pnrel (by rfl) _ hes (by row_entriesB), instOuter_subst_listToVec _ isSemiformula_PshiftG (by rfl) _ hes (by row_entriesB)]
  all_goals try row_entries_simpB
  row_finish

/-! ### `shiftVerumCert` — `“y r. …”`, `m = 2` -/

noncomputable def row_shiftVerumCert_as : List V := [subst LAct (listToVec [bv 1]) Pverum, subst LAct (listToVec [bv 0]) Pverum]
noncomputable def row_shiftVerumCert_c : V := subst LAct (listToVec [bv 0, bv 1]) PshiftG

theorem quote_row_shiftVerumCert : (⌜Semiformula.lMap emb shiftVerumCertB⌝ : V) = impChain LAct row_shiftVerumCert_as row_shiftVerumCert_c := by
  unfold shiftVerumCertB row_shiftVerumCert_as row_shiftVerumCert_c PshiftG Pverum
  all_goals row_shapeB

lemma isSemiformula_shiftVerumCert_c : IsSemiformula LAct ((2 : ℕ) : V) row_shiftVerumCert_c := by
  unfold row_shiftVerumCert_c
  exact isSemiformula_substRow isSemiformula_PshiftG _ (by rfl) (by row_entriesB)

/-- `shiftVerumCert` at the witnesses `[wr, wy]` (the DSL variables right-to-left). -/
lemma inst_shiftVerumCert {wr wy : V} (hwr : IsSemiterm LAct 0 wr) (hwy : IsSemiterm LAct 0 wy) :
    row_shiftVerumCert_as.map (instOuter LAct [wr, wy]) = [verumFact wr, verumFact wy] ∧
    instOuter LAct [wr, wy] row_shiftVerumCert_c = shiftFact wy wr := by
  have hes : ∀ e ∈ ([wr, wy] : List V), IsSemiterm LAct 0 e := (List.forall_mem_cons.mpr ⟨hwr, List.forall_mem_cons.mpr ⟨hwy, List.forall_mem_nil _⟩⟩)
  unfold row_shiftVerumCert_as row_shiftVerumCert_c
  simp only [List.map_cons, List.map_nil]
  rw [instOuter_subst_listToVec _ isSemiformula_Pverum (by rfl) _ hes (by row_entriesB), instOuter_subst_listToVec _ isSemiformula_Pverum (by rfl) _ hes (by row_entriesB), instOuter_subst_listToVec _ isSemiformula_PshiftG (by rfl) _ hes (by row_entriesB)]
  all_goals try row_entries_simpB
  row_finish

/-! ### `shiftFalsumCert` — `“y r. …”`, `m = 2` -/

noncomputable def row_shiftFalsumCert_as : List V := [subst LAct (listToVec [bv 1]) Pfalsum, subst LAct (listToVec [bv 0]) Pfalsum]
noncomputable def row_shiftFalsumCert_c : V := subst LAct (listToVec [bv 0, bv 1]) PshiftG

theorem quote_row_shiftFalsumCert : (⌜Semiformula.lMap emb shiftFalsumCertB⌝ : V) = impChain LAct row_shiftFalsumCert_as row_shiftFalsumCert_c := by
  unfold shiftFalsumCertB row_shiftFalsumCert_as row_shiftFalsumCert_c Pfalsum PshiftG
  all_goals row_shapeB

lemma isSemiformula_shiftFalsumCert_c : IsSemiformula LAct ((2 : ℕ) : V) row_shiftFalsumCert_c := by
  unfold row_shiftFalsumCert_c
  exact isSemiformula_substRow isSemiformula_PshiftG _ (by rfl) (by row_entriesB)

/-- `shiftFalsumCert` at the witnesses `[wr, wy]` (the DSL variables right-to-left). -/
lemma inst_shiftFalsumCert {wr wy : V} (hwr : IsSemiterm LAct 0 wr) (hwy : IsSemiterm LAct 0 wy) :
    row_shiftFalsumCert_as.map (instOuter LAct [wr, wy]) = [falsumFact wr, falsumFact wy] ∧
    instOuter LAct [wr, wy] row_shiftFalsumCert_c = shiftFact wy wr := by
  have hes : ∀ e ∈ ([wr, wy] : List V), IsSemiterm LAct 0 e := (List.forall_mem_cons.mpr ⟨hwr, List.forall_mem_cons.mpr ⟨hwy, List.forall_mem_nil _⟩⟩)
  unfold row_shiftFalsumCert_as row_shiftFalsumCert_c
  simp only [List.map_cons, List.map_nil]
  rw [instOuter_subst_listToVec _ isSemiformula_Pfalsum (by rfl) _ hes (by row_entriesB), instOuter_subst_listToVec _ isSemiformula_Pfalsum (by rfl) _ hes (by row_entriesB), instOuter_subst_listToVec _ isSemiformula_PshiftG (by rfl) _ hes (by row_entriesB)]
  all_goals try row_entries_simpB
  row_finish

/-! ### `shiftAndCert` — `“y sq sp r q p n. …”`, `m = 7` -/

noncomputable def row_shiftAndCert_as : List V := [subst LAct (listToVec [bv 6, bv 5]) Ppi, subst LAct (listToVec [bv 6, bv 4]) Ppi, subst LAct (listToVec [bv 3, bv 5, bv 4]) Pand, subst LAct (listToVec [bv 2, bv 5]) PshiftG, subst LAct (listToVec [bv 1, bv 4]) PshiftG, subst LAct (listToVec [bv 0, bv 2, bv 1]) Pand]
noncomputable def row_shiftAndCert_c : V := subst LAct (listToVec [bv 0, bv 3]) PshiftG

theorem quote_row_shiftAndCert : (⌜Semiformula.lMap emb shiftAndCertB⌝ : V) = impChain LAct row_shiftAndCert_as row_shiftAndCert_c := by
  unfold shiftAndCertB row_shiftAndCert_as row_shiftAndCert_c Pand Ppi PshiftG
  all_goals row_shapeB

lemma isSemiformula_shiftAndCert_c : IsSemiformula LAct ((7 : ℕ) : V) row_shiftAndCert_c := by
  unfold row_shiftAndCert_c
  exact isSemiformula_substRow isSemiformula_PshiftG _ (by rfl) (by row_entriesB)

/-- `shiftAndCert` at the witnesses `[wn, wp, wq, wr, wsp, wsq, wy]` (the DSL variables right-to-left). -/
lemma inst_shiftAndCert {wn wp wq wr wsp wsq wy : V} (hwn : IsSemiterm LAct 0 wn) (hwp : IsSemiterm LAct 0 wp) (hwq : IsSemiterm LAct 0 wq) (hwr : IsSemiterm LAct 0 wr) (hwsp : IsSemiterm LAct 0 wsp) (hwsq : IsSemiterm LAct 0 wsq) (hwy : IsSemiterm LAct 0 wy) :
    row_shiftAndCert_as.map (instOuter LAct [wn, wp, wq, wr, wsp, wsq, wy]) = [piFact wn wp, piFact wn wq, andFact wr wp wq, shiftFact wsp wp, shiftFact wsq wq, andFact wy wsp wsq] ∧
    instOuter LAct [wn, wp, wq, wr, wsp, wsq, wy] row_shiftAndCert_c = shiftFact wy wr := by
  have hes : ∀ e ∈ ([wn, wp, wq, wr, wsp, wsq, wy] : List V), IsSemiterm LAct 0 e := (List.forall_mem_cons.mpr ⟨hwn, List.forall_mem_cons.mpr ⟨hwp, List.forall_mem_cons.mpr ⟨hwq, List.forall_mem_cons.mpr ⟨hwr, List.forall_mem_cons.mpr ⟨hwsp, List.forall_mem_cons.mpr ⟨hwsq, List.forall_mem_cons.mpr ⟨hwy, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩)
  unfold row_shiftAndCert_as row_shiftAndCert_c
  simp only [List.map_cons, List.map_nil]
  rw [instOuter_subst_listToVec _ isSemiformula_Ppi (by rfl) _ hes (by row_entriesB), instOuter_subst_listToVec _ isSemiformula_Ppi (by rfl) _ hes (by row_entriesB), instOuter_subst_listToVec _ isSemiformula_Pand (by rfl) _ hes (by row_entriesB), instOuter_subst_listToVec _ isSemiformula_PshiftG (by rfl) _ hes (by row_entriesB), instOuter_subst_listToVec _ isSemiformula_PshiftG (by rfl) _ hes (by row_entriesB), instOuter_subst_listToVec _ isSemiformula_Pand (by rfl) _ hes (by row_entriesB), instOuter_subst_listToVec _ isSemiformula_PshiftG (by rfl) _ hes (by row_entriesB)]
  all_goals try row_entries_simpB
  row_finish

/-! ### `shiftOrCert` — `“y sq sp r q p n. …”`, `m = 7` -/

noncomputable def row_shiftOrCert_as : List V := [subst LAct (listToVec [bv 6, bv 5]) Ppi, subst LAct (listToVec [bv 6, bv 4]) Ppi, subst LAct (listToVec [bv 3, bv 5, bv 4]) Por, subst LAct (listToVec [bv 2, bv 5]) PshiftG, subst LAct (listToVec [bv 1, bv 4]) PshiftG, subst LAct (listToVec [bv 0, bv 2, bv 1]) Por]
noncomputable def row_shiftOrCert_c : V := subst LAct (listToVec [bv 0, bv 3]) PshiftG

theorem quote_row_shiftOrCert : (⌜Semiformula.lMap emb shiftOrCertB⌝ : V) = impChain LAct row_shiftOrCert_as row_shiftOrCert_c := by
  unfold shiftOrCertB row_shiftOrCert_as row_shiftOrCert_c Por Ppi PshiftG
  all_goals row_shapeB

lemma isSemiformula_shiftOrCert_c : IsSemiformula LAct ((7 : ℕ) : V) row_shiftOrCert_c := by
  unfold row_shiftOrCert_c
  exact isSemiformula_substRow isSemiformula_PshiftG _ (by rfl) (by row_entriesB)

/-- `shiftOrCert` at the witnesses `[wn, wp, wq, wr, wsp, wsq, wy]` (the DSL variables right-to-left). -/
lemma inst_shiftOrCert {wn wp wq wr wsp wsq wy : V} (hwn : IsSemiterm LAct 0 wn) (hwp : IsSemiterm LAct 0 wp) (hwq : IsSemiterm LAct 0 wq) (hwr : IsSemiterm LAct 0 wr) (hwsp : IsSemiterm LAct 0 wsp) (hwsq : IsSemiterm LAct 0 wsq) (hwy : IsSemiterm LAct 0 wy) :
    row_shiftOrCert_as.map (instOuter LAct [wn, wp, wq, wr, wsp, wsq, wy]) = [piFact wn wp, piFact wn wq, orFact wr wp wq, shiftFact wsp wp, shiftFact wsq wq, orFact wy wsp wsq] ∧
    instOuter LAct [wn, wp, wq, wr, wsp, wsq, wy] row_shiftOrCert_c = shiftFact wy wr := by
  have hes : ∀ e ∈ ([wn, wp, wq, wr, wsp, wsq, wy] : List V), IsSemiterm LAct 0 e := (List.forall_mem_cons.mpr ⟨hwn, List.forall_mem_cons.mpr ⟨hwp, List.forall_mem_cons.mpr ⟨hwq, List.forall_mem_cons.mpr ⟨hwr, List.forall_mem_cons.mpr ⟨hwsp, List.forall_mem_cons.mpr ⟨hwsq, List.forall_mem_cons.mpr ⟨hwy, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩)
  unfold row_shiftOrCert_as row_shiftOrCert_c
  simp only [List.map_cons, List.map_nil]
  rw [instOuter_subst_listToVec _ isSemiformula_Ppi (by rfl) _ hes (by row_entriesB), instOuter_subst_listToVec _ isSemiformula_Ppi (by rfl) _ hes (by row_entriesB), instOuter_subst_listToVec _ isSemiformula_Por (by rfl) _ hes (by row_entriesB), instOuter_subst_listToVec _ isSemiformula_PshiftG (by rfl) _ hes (by row_entriesB), instOuter_subst_listToVec _ isSemiformula_PshiftG (by rfl) _ hes (by row_entriesB), instOuter_subst_listToVec _ isSemiformula_Por (by rfl) _ hes (by row_entriesB), instOuter_subst_listToVec _ isSemiformula_PshiftG (by rfl) _ hes (by row_entriesB)]
  all_goals try row_entries_simpB
  row_finish

/-! ### `shiftAllCert` — `“y sp r p n. …”`, `m = 5` -/

noncomputable def row_shiftAllCert_as : List V := [subst LAct (listToVec [(bv 4 ^+ (𝟏 : V)), bv 3]) Ppi, subst LAct (listToVec [bv 2, bv 3]) Pall, subst LAct (listToVec [bv 1, bv 3]) PshiftG, subst LAct (listToVec [bv 0, bv 1]) Pall]
noncomputable def row_shiftAllCert_c : V := subst LAct (listToVec [bv 0, bv 2]) PshiftG

theorem quote_row_shiftAllCert : (⌜Semiformula.lMap emb shiftAllCertB⌝ : V) = impChain LAct row_shiftAllCert_as row_shiftAllCert_c := by
  unfold shiftAllCertB row_shiftAllCert_as row_shiftAllCert_c Pall Ppi PshiftG
  all_goals row_shapeB

lemma isSemiformula_shiftAllCert_c : IsSemiformula LAct ((5 : ℕ) : V) row_shiftAllCert_c := by
  unfold row_shiftAllCert_c
  exact isSemiformula_substRow isSemiformula_PshiftG _ (by rfl) (by row_entriesB)

/-- `shiftAllCert` at the witnesses `[wn, wp, wr, wsp, wy]` (the DSL variables right-to-left). -/
lemma inst_shiftAllCert {wn wp wr wsp wy : V} (hwn : IsSemiterm LAct 0 wn) (hwp : IsSemiterm LAct 0 wp) (hwr : IsSemiterm LAct 0 wr) (hwsp : IsSemiterm LAct 0 wsp) (hwy : IsSemiterm LAct 0 wy) :
    row_shiftAllCert_as.map (instOuter LAct [wn, wp, wr, wsp, wy]) = [piFact (wn ^+ (𝟏 : V)) wp, allFact wr wp, shiftFact wsp wp, allFact wy wsp] ∧
    instOuter LAct [wn, wp, wr, wsp, wy] row_shiftAllCert_c = shiftFact wy wr := by
  have hes : ∀ e ∈ ([wn, wp, wr, wsp, wy] : List V), IsSemiterm LAct 0 e := (List.forall_mem_cons.mpr ⟨hwn, List.forall_mem_cons.mpr ⟨hwp, List.forall_mem_cons.mpr ⟨hwr, List.forall_mem_cons.mpr ⟨hwsp, List.forall_mem_cons.mpr ⟨hwy, List.forall_mem_nil _⟩⟩⟩⟩⟩)
  unfold row_shiftAllCert_as row_shiftAllCert_c
  simp only [List.map_cons, List.map_nil]
  rw [instOuter_subst_listToVec _ isSemiformula_Ppi (by rfl) _ hes (by row_entriesB), instOuter_subst_listToVec _ isSemiformula_Pall (by rfl) _ hes (by row_entriesB), instOuter_subst_listToVec _ isSemiformula_PshiftG (by rfl) _ hes (by row_entriesB), instOuter_subst_listToVec _ isSemiformula_Pall (by rfl) _ hes (by row_entriesB), instOuter_subst_listToVec _ isSemiformula_PshiftG (by rfl) _ hes (by row_entriesB)]
  all_goals try row_entries_simpB
  row_finish

/-! ### `shiftExsCert` — `“y sp r p n. …”`, `m = 5` -/

noncomputable def row_shiftExsCert_as : List V := [subst LAct (listToVec [(bv 4 ^+ (𝟏 : V)), bv 3]) Ppi, subst LAct (listToVec [bv 2, bv 3]) Pexs, subst LAct (listToVec [bv 1, bv 3]) PshiftG, subst LAct (listToVec [bv 0, bv 1]) Pexs]
noncomputable def row_shiftExsCert_c : V := subst LAct (listToVec [bv 0, bv 2]) PshiftG

theorem quote_row_shiftExsCert : (⌜Semiformula.lMap emb shiftExsCertB⌝ : V) = impChain LAct row_shiftExsCert_as row_shiftExsCert_c := by
  unfold shiftExsCertB row_shiftExsCert_as row_shiftExsCert_c Pexs Ppi PshiftG
  all_goals row_shapeB

lemma isSemiformula_shiftExsCert_c : IsSemiformula LAct ((5 : ℕ) : V) row_shiftExsCert_c := by
  unfold row_shiftExsCert_c
  exact isSemiformula_substRow isSemiformula_PshiftG _ (by rfl) (by row_entriesB)

/-- `shiftExsCert` at the witnesses `[wn, wp, wr, wsp, wy]` (the DSL variables right-to-left). -/
lemma inst_shiftExsCert {wn wp wr wsp wy : V} (hwn : IsSemiterm LAct 0 wn) (hwp : IsSemiterm LAct 0 wp) (hwr : IsSemiterm LAct 0 wr) (hwsp : IsSemiterm LAct 0 wsp) (hwy : IsSemiterm LAct 0 wy) :
    row_shiftExsCert_as.map (instOuter LAct [wn, wp, wr, wsp, wy]) = [piFact (wn ^+ (𝟏 : V)) wp, exsFact wr wp, shiftFact wsp wp, exsFact wy wsp] ∧
    instOuter LAct [wn, wp, wr, wsp, wy] row_shiftExsCert_c = shiftFact wy wr := by
  have hes : ∀ e ∈ ([wn, wp, wr, wsp, wy] : List V), IsSemiterm LAct 0 e := (List.forall_mem_cons.mpr ⟨hwn, List.forall_mem_cons.mpr ⟨hwp, List.forall_mem_cons.mpr ⟨hwr, List.forall_mem_cons.mpr ⟨hwsp, List.forall_mem_cons.mpr ⟨hwy, List.forall_mem_nil _⟩⟩⟩⟩⟩)
  unfold row_shiftExsCert_as row_shiftExsCert_c
  simp only [List.map_cons, List.map_nil]
  rw [instOuter_subst_listToVec _ isSemiformula_Ppi (by rfl) _ hes (by row_entriesB), instOuter_subst_listToVec _ isSemiformula_Pexs (by rfl) _ hes (by row_entriesB), instOuter_subst_listToVec _ isSemiformula_PshiftG (by rfl) _ hes (by row_entriesB), instOuter_subst_listToVec _ isSemiformula_Pexs (by rfl) _ hes (by row_entriesB), instOuter_subst_listToVec _ isSemiformula_PshiftG (by rfl) _ hes (by row_entriesB)]
  all_goals try row_entries_simpB
  row_finish

/-! ### `substsRelCert` — `“y u v R k r w. …”`, `m = 7` -/

noncomputable def row_substsRelCert_as : List V := [subst LAct (listToVec [bv 4, bv 3]) PisRel, subst LAct (listToVec [bv 4, bv 2]) PutvPi, subst LAct (listToVec [bv 5, bv 4, bv 3, bv 2]) Prel, subst LAct (listToVec [bv 1, bv 4, bv 6, bv 2]) PtsvG, subst LAct (listToVec [bv 0, bv 4, bv 3, bv 1]) Prel]
noncomputable def row_substsRelCert_c : V := subst LAct (listToVec [bv 0, bv 6, bv 5]) PsubstsG

theorem quote_row_substsRelCert : (⌜Semiformula.lMap emb substsRelCertB⌝ : V) = impChain LAct row_substsRelCert_as row_substsRelCert_c := by
  unfold substsRelCertB row_substsRelCert_as row_substsRelCert_c PisRel Prel PsubstsG PtsvG PutvPi
  all_goals row_shapeB

lemma isSemiformula_substsRelCert_c : IsSemiformula LAct ((7 : ℕ) : V) row_substsRelCert_c := by
  unfold row_substsRelCert_c
  exact isSemiformula_substRow isSemiformula_PsubstsG _ (by rfl) (by row_entriesB)

/-- `substsRelCert` at the witnesses `[ww, wr, wk, wR, wv, wu, wy]` (the DSL variables right-to-left). -/
lemma inst_substsRelCert {ww wr wk wR wv wu wy : V} (hww : IsSemiterm LAct 0 ww) (hwr : IsSemiterm LAct 0 wr) (hwk : IsSemiterm LAct 0 wk) (hwR : IsSemiterm LAct 0 wR) (hwv : IsSemiterm LAct 0 wv) (hwu : IsSemiterm LAct 0 wu) (hwy : IsSemiterm LAct 0 wy) :
    row_substsRelCert_as.map (instOuter LAct [ww, wr, wk, wR, wv, wu, wy]) = [isRelFact wk wR, utvPiFact wk wv, relFact wr wk wR wv, tsvFact wu wk ww wv, relFact wy wk wR wu] ∧
    instOuter LAct [ww, wr, wk, wR, wv, wu, wy] row_substsRelCert_c = substFact wy ww wr := by
  have hes : ∀ e ∈ ([ww, wr, wk, wR, wv, wu, wy] : List V), IsSemiterm LAct 0 e := (List.forall_mem_cons.mpr ⟨hww, List.forall_mem_cons.mpr ⟨hwr, List.forall_mem_cons.mpr ⟨hwk, List.forall_mem_cons.mpr ⟨hwR, List.forall_mem_cons.mpr ⟨hwv, List.forall_mem_cons.mpr ⟨hwu, List.forall_mem_cons.mpr ⟨hwy, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩)
  unfold row_substsRelCert_as row_substsRelCert_c
  simp only [List.map_cons, List.map_nil]
  rw [instOuter_subst_listToVec _ isSemiformula_PisRel (by rfl) _ hes (by row_entriesB), instOuter_subst_listToVec _ isSemiformula_PutvPi (by rfl) _ hes (by row_entriesB), instOuter_subst_listToVec _ isSemiformula_Prel (by rfl) _ hes (by row_entriesB), instOuter_subst_listToVec _ isSemiformula_PtsvG (by rfl) _ hes (by row_entriesB), instOuter_subst_listToVec _ isSemiformula_Prel (by rfl) _ hes (by row_entriesB), instOuter_subst_listToVec _ isSemiformula_PsubstsG (by rfl) _ hes (by row_entriesB)]
  all_goals try row_entries_simpB
  row_finish

/-! ### `substsNRelCert` — `“y u v R k r w. …”`, `m = 7` -/

noncomputable def row_substsNRelCert_as : List V := [subst LAct (listToVec [bv 4, bv 3]) PisRel, subst LAct (listToVec [bv 4, bv 2]) PutvPi, subst LAct (listToVec [bv 5, bv 4, bv 3, bv 2]) Pnrel, subst LAct (listToVec [bv 1, bv 4, bv 6, bv 2]) PtsvG, subst LAct (listToVec [bv 0, bv 4, bv 3, bv 1]) Pnrel]
noncomputable def row_substsNRelCert_c : V := subst LAct (listToVec [bv 0, bv 6, bv 5]) PsubstsG

theorem quote_row_substsNRelCert : (⌜Semiformula.lMap emb substsNRelCertB⌝ : V) = impChain LAct row_substsNRelCert_as row_substsNRelCert_c := by
  unfold substsNRelCertB row_substsNRelCert_as row_substsNRelCert_c PisRel Pnrel PsubstsG PtsvG PutvPi
  all_goals row_shapeB

lemma isSemiformula_substsNRelCert_c : IsSemiformula LAct ((7 : ℕ) : V) row_substsNRelCert_c := by
  unfold row_substsNRelCert_c
  exact isSemiformula_substRow isSemiformula_PsubstsG _ (by rfl) (by row_entriesB)

/-- `substsNRelCert` at the witnesses `[ww, wr, wk, wR, wv, wu, wy]` (the DSL variables right-to-left). -/
lemma inst_substsNRelCert {ww wr wk wR wv wu wy : V} (hww : IsSemiterm LAct 0 ww) (hwr : IsSemiterm LAct 0 wr) (hwk : IsSemiterm LAct 0 wk) (hwR : IsSemiterm LAct 0 wR) (hwv : IsSemiterm LAct 0 wv) (hwu : IsSemiterm LAct 0 wu) (hwy : IsSemiterm LAct 0 wy) :
    row_substsNRelCert_as.map (instOuter LAct [ww, wr, wk, wR, wv, wu, wy]) = [isRelFact wk wR, utvPiFact wk wv, nrelFact wr wk wR wv, tsvFact wu wk ww wv, nrelFact wy wk wR wu] ∧
    instOuter LAct [ww, wr, wk, wR, wv, wu, wy] row_substsNRelCert_c = substFact wy ww wr := by
  have hes : ∀ e ∈ ([ww, wr, wk, wR, wv, wu, wy] : List V), IsSemiterm LAct 0 e := (List.forall_mem_cons.mpr ⟨hww, List.forall_mem_cons.mpr ⟨hwr, List.forall_mem_cons.mpr ⟨hwk, List.forall_mem_cons.mpr ⟨hwR, List.forall_mem_cons.mpr ⟨hwv, List.forall_mem_cons.mpr ⟨hwu, List.forall_mem_cons.mpr ⟨hwy, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩)
  unfold row_substsNRelCert_as row_substsNRelCert_c
  simp only [List.map_cons, List.map_nil]
  rw [instOuter_subst_listToVec _ isSemiformula_PisRel (by rfl) _ hes (by row_entriesB), instOuter_subst_listToVec _ isSemiformula_PutvPi (by rfl) _ hes (by row_entriesB), instOuter_subst_listToVec _ isSemiformula_Pnrel (by rfl) _ hes (by row_entriesB), instOuter_subst_listToVec _ isSemiformula_PtsvG (by rfl) _ hes (by row_entriesB), instOuter_subst_listToVec _ isSemiformula_Pnrel (by rfl) _ hes (by row_entriesB), instOuter_subst_listToVec _ isSemiformula_PsubstsG (by rfl) _ hes (by row_entriesB)]
  all_goals try row_entries_simpB
  row_finish

/-! ### `substsVerumCert` — `“y r w. …”`, `m = 3` -/

noncomputable def row_substsVerumCert_as : List V := [subst LAct (listToVec [bv 1]) Pverum, subst LAct (listToVec [bv 0]) Pverum]
noncomputable def row_substsVerumCert_c : V := subst LAct (listToVec [bv 0, bv 2, bv 1]) PsubstsG

theorem quote_row_substsVerumCert : (⌜Semiformula.lMap emb substsVerumCertB⌝ : V) = impChain LAct row_substsVerumCert_as row_substsVerumCert_c := by
  unfold substsVerumCertB row_substsVerumCert_as row_substsVerumCert_c PsubstsG Pverum
  all_goals row_shapeB

lemma isSemiformula_substsVerumCert_c : IsSemiformula LAct ((3 : ℕ) : V) row_substsVerumCert_c := by
  unfold row_substsVerumCert_c
  exact isSemiformula_substRow isSemiformula_PsubstsG _ (by rfl) (by row_entriesB)

/-- `substsVerumCert` at the witnesses `[ww, wr, wy]` (the DSL variables right-to-left). -/
lemma inst_substsVerumCert {ww wr wy : V} (hww : IsSemiterm LAct 0 ww) (hwr : IsSemiterm LAct 0 wr) (hwy : IsSemiterm LAct 0 wy) :
    row_substsVerumCert_as.map (instOuter LAct [ww, wr, wy]) = [verumFact wr, verumFact wy] ∧
    instOuter LAct [ww, wr, wy] row_substsVerumCert_c = substFact wy ww wr := by
  have hes : ∀ e ∈ ([ww, wr, wy] : List V), IsSemiterm LAct 0 e := (List.forall_mem_cons.mpr ⟨hww, List.forall_mem_cons.mpr ⟨hwr, List.forall_mem_cons.mpr ⟨hwy, List.forall_mem_nil _⟩⟩⟩)
  unfold row_substsVerumCert_as row_substsVerumCert_c
  simp only [List.map_cons, List.map_nil]
  rw [instOuter_subst_listToVec _ isSemiformula_Pverum (by rfl) _ hes (by row_entriesB), instOuter_subst_listToVec _ isSemiformula_Pverum (by rfl) _ hes (by row_entriesB), instOuter_subst_listToVec _ isSemiformula_PsubstsG (by rfl) _ hes (by row_entriesB)]
  all_goals try row_entries_simpB
  row_finish

/-! ### `substsFalsumCert` — `“y r w. …”`, `m = 3` -/

noncomputable def row_substsFalsumCert_as : List V := [subst LAct (listToVec [bv 1]) Pfalsum, subst LAct (listToVec [bv 0]) Pfalsum]
noncomputable def row_substsFalsumCert_c : V := subst LAct (listToVec [bv 0, bv 2, bv 1]) PsubstsG

theorem quote_row_substsFalsumCert : (⌜Semiformula.lMap emb substsFalsumCertB⌝ : V) = impChain LAct row_substsFalsumCert_as row_substsFalsumCert_c := by
  unfold substsFalsumCertB row_substsFalsumCert_as row_substsFalsumCert_c Pfalsum PsubstsG
  all_goals row_shapeB

lemma isSemiformula_substsFalsumCert_c : IsSemiformula LAct ((3 : ℕ) : V) row_substsFalsumCert_c := by
  unfold row_substsFalsumCert_c
  exact isSemiformula_substRow isSemiformula_PsubstsG _ (by rfl) (by row_entriesB)

/-- `substsFalsumCert` at the witnesses `[ww, wr, wy]` (the DSL variables right-to-left). -/
lemma inst_substsFalsumCert {ww wr wy : V} (hww : IsSemiterm LAct 0 ww) (hwr : IsSemiterm LAct 0 wr) (hwy : IsSemiterm LAct 0 wy) :
    row_substsFalsumCert_as.map (instOuter LAct [ww, wr, wy]) = [falsumFact wr, falsumFact wy] ∧
    instOuter LAct [ww, wr, wy] row_substsFalsumCert_c = substFact wy ww wr := by
  have hes : ∀ e ∈ ([ww, wr, wy] : List V), IsSemiterm LAct 0 e := (List.forall_mem_cons.mpr ⟨hww, List.forall_mem_cons.mpr ⟨hwr, List.forall_mem_cons.mpr ⟨hwy, List.forall_mem_nil _⟩⟩⟩)
  unfold row_substsFalsumCert_as row_substsFalsumCert_c
  simp only [List.map_cons, List.map_nil]
  rw [instOuter_subst_listToVec _ isSemiformula_Pfalsum (by rfl) _ hes (by row_entriesB), instOuter_subst_listToVec _ isSemiformula_Pfalsum (by rfl) _ hes (by row_entriesB), instOuter_subst_listToVec _ isSemiformula_PsubstsG (by rfl) _ hes (by row_entriesB)]
  all_goals try row_entries_simpB
  row_finish

/-! ### `substsAndCert` — `“y sq sp r q p n w. …”`, `m = 8` -/

noncomputable def row_substsAndCert_as : List V := [subst LAct (listToVec [bv 6, bv 5]) Ppi, subst LAct (listToVec [bv 6, bv 4]) Ppi, subst LAct (listToVec [bv 3, bv 5, bv 4]) Pand, subst LAct (listToVec [bv 2, bv 7, bv 5]) PsubstsG, subst LAct (listToVec [bv 1, bv 7, bv 4]) PsubstsG, subst LAct (listToVec [bv 0, bv 2, bv 1]) Pand]
noncomputable def row_substsAndCert_c : V := subst LAct (listToVec [bv 0, bv 7, bv 3]) PsubstsG

theorem quote_row_substsAndCert : (⌜Semiformula.lMap emb substsAndCertB⌝ : V) = impChain LAct row_substsAndCert_as row_substsAndCert_c := by
  unfold substsAndCertB row_substsAndCert_as row_substsAndCert_c Pand Ppi PsubstsG
  all_goals row_shapeB

lemma isSemiformula_substsAndCert_c : IsSemiformula LAct ((8 : ℕ) : V) row_substsAndCert_c := by
  unfold row_substsAndCert_c
  exact isSemiformula_substRow isSemiformula_PsubstsG _ (by rfl) (by row_entriesB)

/-- `substsAndCert` at the witnesses `[ww, wn, wp, wq, wr, wsp, wsq, wy]` (the DSL variables right-to-left). -/
lemma inst_substsAndCert {ww wn wp wq wr wsp wsq wy : V} (hww : IsSemiterm LAct 0 ww) (hwn : IsSemiterm LAct 0 wn) (hwp : IsSemiterm LAct 0 wp) (hwq : IsSemiterm LAct 0 wq) (hwr : IsSemiterm LAct 0 wr) (hwsp : IsSemiterm LAct 0 wsp) (hwsq : IsSemiterm LAct 0 wsq) (hwy : IsSemiterm LAct 0 wy) :
    row_substsAndCert_as.map (instOuter LAct [ww, wn, wp, wq, wr, wsp, wsq, wy]) = [piFact wn wp, piFact wn wq, andFact wr wp wq, substFact wsp ww wp, substFact wsq ww wq, andFact wy wsp wsq] ∧
    instOuter LAct [ww, wn, wp, wq, wr, wsp, wsq, wy] row_substsAndCert_c = substFact wy ww wr := by
  have hes : ∀ e ∈ ([ww, wn, wp, wq, wr, wsp, wsq, wy] : List V), IsSemiterm LAct 0 e := (List.forall_mem_cons.mpr ⟨hww, List.forall_mem_cons.mpr ⟨hwn, List.forall_mem_cons.mpr ⟨hwp, List.forall_mem_cons.mpr ⟨hwq, List.forall_mem_cons.mpr ⟨hwr, List.forall_mem_cons.mpr ⟨hwsp, List.forall_mem_cons.mpr ⟨hwsq, List.forall_mem_cons.mpr ⟨hwy, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩)
  unfold row_substsAndCert_as row_substsAndCert_c
  simp only [List.map_cons, List.map_nil]
  rw [instOuter_subst_listToVec _ isSemiformula_Ppi (by rfl) _ hes (by row_entriesB), instOuter_subst_listToVec _ isSemiformula_Ppi (by rfl) _ hes (by row_entriesB), instOuter_subst_listToVec _ isSemiformula_Pand (by rfl) _ hes (by row_entriesB), instOuter_subst_listToVec _ isSemiformula_PsubstsG (by rfl) _ hes (by row_entriesB), instOuter_subst_listToVec _ isSemiformula_PsubstsG (by rfl) _ hes (by row_entriesB), instOuter_subst_listToVec _ isSemiformula_Pand (by rfl) _ hes (by row_entriesB), instOuter_subst_listToVec _ isSemiformula_PsubstsG (by rfl) _ hes (by row_entriesB)]
  all_goals try row_entries_simpB
  row_finish

/-! ### `substsOrCert` — `“y sq sp r q p n w. …”`, `m = 8` -/

noncomputable def row_substsOrCert_as : List V := [subst LAct (listToVec [bv 6, bv 5]) Ppi, subst LAct (listToVec [bv 6, bv 4]) Ppi, subst LAct (listToVec [bv 3, bv 5, bv 4]) Por, subst LAct (listToVec [bv 2, bv 7, bv 5]) PsubstsG, subst LAct (listToVec [bv 1, bv 7, bv 4]) PsubstsG, subst LAct (listToVec [bv 0, bv 2, bv 1]) Por]
noncomputable def row_substsOrCert_c : V := subst LAct (listToVec [bv 0, bv 7, bv 3]) PsubstsG

theorem quote_row_substsOrCert : (⌜Semiformula.lMap emb substsOrCertB⌝ : V) = impChain LAct row_substsOrCert_as row_substsOrCert_c := by
  unfold substsOrCertB row_substsOrCert_as row_substsOrCert_c Por Ppi PsubstsG
  all_goals row_shapeB

lemma isSemiformula_substsOrCert_c : IsSemiformula LAct ((8 : ℕ) : V) row_substsOrCert_c := by
  unfold row_substsOrCert_c
  exact isSemiformula_substRow isSemiformula_PsubstsG _ (by rfl) (by row_entriesB)

/-- `substsOrCert` at the witnesses `[ww, wn, wp, wq, wr, wsp, wsq, wy]` (the DSL variables right-to-left). -/
lemma inst_substsOrCert {ww wn wp wq wr wsp wsq wy : V} (hww : IsSemiterm LAct 0 ww) (hwn : IsSemiterm LAct 0 wn) (hwp : IsSemiterm LAct 0 wp) (hwq : IsSemiterm LAct 0 wq) (hwr : IsSemiterm LAct 0 wr) (hwsp : IsSemiterm LAct 0 wsp) (hwsq : IsSemiterm LAct 0 wsq) (hwy : IsSemiterm LAct 0 wy) :
    row_substsOrCert_as.map (instOuter LAct [ww, wn, wp, wq, wr, wsp, wsq, wy]) = [piFact wn wp, piFact wn wq, orFact wr wp wq, substFact wsp ww wp, substFact wsq ww wq, orFact wy wsp wsq] ∧
    instOuter LAct [ww, wn, wp, wq, wr, wsp, wsq, wy] row_substsOrCert_c = substFact wy ww wr := by
  have hes : ∀ e ∈ ([ww, wn, wp, wq, wr, wsp, wsq, wy] : List V), IsSemiterm LAct 0 e := (List.forall_mem_cons.mpr ⟨hww, List.forall_mem_cons.mpr ⟨hwn, List.forall_mem_cons.mpr ⟨hwp, List.forall_mem_cons.mpr ⟨hwq, List.forall_mem_cons.mpr ⟨hwr, List.forall_mem_cons.mpr ⟨hwsp, List.forall_mem_cons.mpr ⟨hwsq, List.forall_mem_cons.mpr ⟨hwy, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩)
  unfold row_substsOrCert_as row_substsOrCert_c
  simp only [List.map_cons, List.map_nil]
  rw [instOuter_subst_listToVec _ isSemiformula_Ppi (by rfl) _ hes (by row_entriesB), instOuter_subst_listToVec _ isSemiformula_Ppi (by rfl) _ hes (by row_entriesB), instOuter_subst_listToVec _ isSemiformula_Por (by rfl) _ hes (by row_entriesB), instOuter_subst_listToVec _ isSemiformula_PsubstsG (by rfl) _ hes (by row_entriesB), instOuter_subst_listToVec _ isSemiformula_PsubstsG (by rfl) _ hes (by row_entriesB), instOuter_subst_listToVec _ isSemiformula_Por (by rfl) _ hes (by row_entriesB), instOuter_subst_listToVec _ isSemiformula_PsubstsG (by rfl) _ hes (by row_entriesB)]
  all_goals try row_entries_simpB
  row_finish

/-! ### `substsAllCert` — `“y sp u r p n w. …”`, `m = 7` -/

noncomputable def row_substsAllCert_as : List V := [subst LAct (listToVec [(bv 5 ^+ (𝟏 : V)), bv 4]) Ppi, subst LAct (listToVec [bv 3, bv 4]) Pall, subst LAct (listToVec [bv 2, bv 6]) PqVecG, subst LAct (listToVec [bv 1, bv 2, bv 4]) PsubstsG, subst LAct (listToVec [bv 0, bv 1]) Pall]
noncomputable def row_substsAllCert_c : V := subst LAct (listToVec [bv 0, bv 6, bv 3]) PsubstsG

theorem quote_row_substsAllCert : (⌜Semiformula.lMap emb substsAllCertB⌝ : V) = impChain LAct row_substsAllCert_as row_substsAllCert_c := by
  unfold substsAllCertB row_substsAllCert_as row_substsAllCert_c Pall Ppi PqVecG PsubstsG
  all_goals row_shapeB

lemma isSemiformula_substsAllCert_c : IsSemiformula LAct ((7 : ℕ) : V) row_substsAllCert_c := by
  unfold row_substsAllCert_c
  exact isSemiformula_substRow isSemiformula_PsubstsG _ (by rfl) (by row_entriesB)

/-- `substsAllCert` at the witnesses `[ww, wn, wp, wr, wu, wsp, wy]` (the DSL variables right-to-left). -/
lemma inst_substsAllCert {ww wn wp wr wu wsp wy : V} (hww : IsSemiterm LAct 0 ww) (hwn : IsSemiterm LAct 0 wn) (hwp : IsSemiterm LAct 0 wp) (hwr : IsSemiterm LAct 0 wr) (hwu : IsSemiterm LAct 0 wu) (hwsp : IsSemiterm LAct 0 wsp) (hwy : IsSemiterm LAct 0 wy) :
    row_substsAllCert_as.map (instOuter LAct [ww, wn, wp, wr, wu, wsp, wy]) = [piFact (wn ^+ (𝟏 : V)) wp, allFact wr wp, qVecFact wu ww, substFact wsp wu wp, allFact wy wsp] ∧
    instOuter LAct [ww, wn, wp, wr, wu, wsp, wy] row_substsAllCert_c = substFact wy ww wr := by
  have hes : ∀ e ∈ ([ww, wn, wp, wr, wu, wsp, wy] : List V), IsSemiterm LAct 0 e := (List.forall_mem_cons.mpr ⟨hww, List.forall_mem_cons.mpr ⟨hwn, List.forall_mem_cons.mpr ⟨hwp, List.forall_mem_cons.mpr ⟨hwr, List.forall_mem_cons.mpr ⟨hwu, List.forall_mem_cons.mpr ⟨hwsp, List.forall_mem_cons.mpr ⟨hwy, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩)
  unfold row_substsAllCert_as row_substsAllCert_c
  simp only [List.map_cons, List.map_nil]
  rw [instOuter_subst_listToVec _ isSemiformula_Ppi (by rfl) _ hes (by row_entriesB), instOuter_subst_listToVec _ isSemiformula_Pall (by rfl) _ hes (by row_entriesB), instOuter_subst_listToVec _ isSemiformula_PqVecG (by rfl) _ hes (by row_entriesB), instOuter_subst_listToVec _ isSemiformula_PsubstsG (by rfl) _ hes (by row_entriesB), instOuter_subst_listToVec _ isSemiformula_Pall (by rfl) _ hes (by row_entriesB), instOuter_subst_listToVec _ isSemiformula_PsubstsG (by rfl) _ hes (by row_entriesB)]
  all_goals try row_entries_simpB
  row_finish

/-! ### `substsExsCert` — `“y sp u r p n w. …”`, `m = 7` -/

noncomputable def row_substsExsCert_as : List V := [subst LAct (listToVec [(bv 5 ^+ (𝟏 : V)), bv 4]) Ppi, subst LAct (listToVec [bv 3, bv 4]) Pexs, subst LAct (listToVec [bv 2, bv 6]) PqVecG, subst LAct (listToVec [bv 1, bv 2, bv 4]) PsubstsG, subst LAct (listToVec [bv 0, bv 1]) Pexs]
noncomputable def row_substsExsCert_c : V := subst LAct (listToVec [bv 0, bv 6, bv 3]) PsubstsG

theorem quote_row_substsExsCert : (⌜Semiformula.lMap emb substsExsCertB⌝ : V) = impChain LAct row_substsExsCert_as row_substsExsCert_c := by
  unfold substsExsCertB row_substsExsCert_as row_substsExsCert_c Pexs Ppi PqVecG PsubstsG
  all_goals row_shapeB

lemma isSemiformula_substsExsCert_c : IsSemiformula LAct ((7 : ℕ) : V) row_substsExsCert_c := by
  unfold row_substsExsCert_c
  exact isSemiformula_substRow isSemiformula_PsubstsG _ (by rfl) (by row_entriesB)

/-- `substsExsCert` at the witnesses `[ww, wn, wp, wr, wu, wsp, wy]` (the DSL variables right-to-left). -/
lemma inst_substsExsCert {ww wn wp wr wu wsp wy : V} (hww : IsSemiterm LAct 0 ww) (hwn : IsSemiterm LAct 0 wn) (hwp : IsSemiterm LAct 0 wp) (hwr : IsSemiterm LAct 0 wr) (hwu : IsSemiterm LAct 0 wu) (hwsp : IsSemiterm LAct 0 wsp) (hwy : IsSemiterm LAct 0 wy) :
    row_substsExsCert_as.map (instOuter LAct [ww, wn, wp, wr, wu, wsp, wy]) = [piFact (wn ^+ (𝟏 : V)) wp, exsFact wr wp, qVecFact wu ww, substFact wsp wu wp, exsFact wy wsp] ∧
    instOuter LAct [ww, wn, wp, wr, wu, wsp, wy] row_substsExsCert_c = substFact wy ww wr := by
  have hes : ∀ e ∈ ([ww, wn, wp, wr, wu, wsp, wy] : List V), IsSemiterm LAct 0 e := (List.forall_mem_cons.mpr ⟨hww, List.forall_mem_cons.mpr ⟨hwn, List.forall_mem_cons.mpr ⟨hwp, List.forall_mem_cons.mpr ⟨hwr, List.forall_mem_cons.mpr ⟨hwu, List.forall_mem_cons.mpr ⟨hwsp, List.forall_mem_cons.mpr ⟨hwy, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩)
  unfold row_substsExsCert_as row_substsExsCert_c
  simp only [List.map_cons, List.map_nil]
  rw [instOuter_subst_listToVec _ isSemiformula_Ppi (by rfl) _ hes (by row_entriesB), instOuter_subst_listToVec _ isSemiformula_Pexs (by rfl) _ hes (by row_entriesB), instOuter_subst_listToVec _ isSemiformula_PqVecG (by rfl) _ hes (by row_entriesB), instOuter_subst_listToVec _ isSemiformula_PsubstsG (by rfl) _ hes (by row_entriesB), instOuter_subst_listToVec _ isSemiformula_Pexs (by rfl) _ hes (by row_entriesB), instOuter_subst_listToVec _ isSemiformula_PsubstsG (by rfl) _ hes (by row_entriesB)]
  all_goals try row_entries_simpB
  row_finish

/-! ### `freeCert` — `“fp sp z p. …”`, `m = 4` -/

noncomputable def row_freeCert_as : List V := [subst LAct (listToVec [bv 2, (𝟎 : V)]) Pfvar, subst LAct (listToVec [bv 1, bv 3]) PshiftG, subst LAct (listToVec [bv 0, bv 2, bv 1]) Psubsts1G]
noncomputable def row_freeCert_c : V := subst LAct (listToVec [bv 0, bv 3]) PfreeG

theorem quote_row_freeCert : (⌜Semiformula.lMap emb freeCertB⌝ : V) = impChain LAct row_freeCert_as row_freeCert_c := by
  unfold freeCertB row_freeCert_as row_freeCert_c PfreeG Pfvar PshiftG Psubsts1G
  all_goals row_shapeB

lemma isSemiformula_freeCert_c : IsSemiformula LAct ((4 : ℕ) : V) row_freeCert_c := by
  unfold row_freeCert_c
  exact isSemiformula_substRow isSemiformula_PfreeG _ (by rfl) (by row_entriesB)

/-- `freeCert` at the witnesses `[wp, wz, wsp, wfp]` (the DSL variables right-to-left). -/
lemma inst_freeCert {wp wz wsp wfp : V} (hwp : IsSemiterm LAct 0 wp) (hwz : IsSemiterm LAct 0 wz) (hwsp : IsSemiterm LAct 0 wsp) (hwfp : IsSemiterm LAct 0 wfp) :
    row_freeCert_as.map (instOuter LAct [wp, wz, wsp, wfp]) = [fvarFact wz (𝟎 : V), shiftFact wsp wp, substs1Fact wfp wz wsp] ∧
    instOuter LAct [wp, wz, wsp, wfp] row_freeCert_c = freeFact wfp wp := by
  have hes : ∀ e ∈ ([wp, wz, wsp, wfp] : List V), IsSemiterm LAct 0 e := (List.forall_mem_cons.mpr ⟨hwp, List.forall_mem_cons.mpr ⟨hwz, List.forall_mem_cons.mpr ⟨hwsp, List.forall_mem_cons.mpr ⟨hwfp, List.forall_mem_nil _⟩⟩⟩⟩)
  unfold row_freeCert_as row_freeCert_c
  simp only [List.map_cons, List.map_nil]
  rw [instOuter_subst_listToVec _ isSemiformula_Pfvar (by rfl) _ hes (by row_entriesB), instOuter_subst_listToVec _ isSemiformula_PshiftG (by rfl) _ hes (by row_entriesB), instOuter_subst_listToVec _ isSemiformula_Psubsts1G (by rfl) _ hes (by row_entriesB), instOuter_subst_listToVec _ isSemiformula_PfreeG (by rfl) _ hes (by row_entriesB)]
  all_goals try row_entries_simpB
  row_finish

/-! ### `substsSubsts1` — `“y w t p. …”`, `m = 4` -/

noncomputable def row_substsSubsts1_as : List V := [subst LAct (listToVec [bv 1, bv 2, (𝟎 : V)]) Padjoin, subst LAct (listToVec [bv 0, bv 1, bv 3]) PsubstsG]
noncomputable def row_substsSubsts1_c : V := subst LAct (listToVec [bv 0, bv 2, bv 3]) Psubsts1G

theorem quote_row_substsSubsts1 : (⌜Semiformula.lMap emb substsSubsts1B⌝ : V) = impChain LAct row_substsSubsts1_as row_substsSubsts1_c := by
  unfold substsSubsts1B row_substsSubsts1_as row_substsSubsts1_c Padjoin Psubsts1G PsubstsG
  all_goals row_shapeB

lemma isSemiformula_substsSubsts1_c : IsSemiformula LAct ((4 : ℕ) : V) row_substsSubsts1_c := by
  unfold row_substsSubsts1_c
  exact isSemiformula_substRow isSemiformula_Psubsts1G _ (by rfl) (by row_entriesB)

/-- `substsSubsts1` at the witnesses `[wp, wt, ww, wy]` (the DSL variables right-to-left). -/
lemma inst_substsSubsts1 {wp wt ww wy : V} (hwp : IsSemiterm LAct 0 wp) (hwt : IsSemiterm LAct 0 wt) (hww : IsSemiterm LAct 0 ww) (hwy : IsSemiterm LAct 0 wy) :
    row_substsSubsts1_as.map (instOuter LAct [wp, wt, ww, wy]) = [adjFact ww wt (𝟎 : V), substFact wy ww wp] ∧
    instOuter LAct [wp, wt, ww, wy] row_substsSubsts1_c = substs1Fact wy wt wp := by
  have hes : ∀ e ∈ ([wp, wt, ww, wy] : List V), IsSemiterm LAct 0 e := (List.forall_mem_cons.mpr ⟨hwp, List.forall_mem_cons.mpr ⟨hwt, List.forall_mem_cons.mpr ⟨hww, List.forall_mem_cons.mpr ⟨hwy, List.forall_mem_nil _⟩⟩⟩⟩)
  unfold row_substsSubsts1_as row_substsSubsts1_c
  simp only [List.map_cons, List.map_nil]
  rw [instOuter_subst_listToVec _ isSemiformula_Padjoin (by rfl) _ hes (by row_entriesB), instOuter_subst_listToVec _ isSemiformula_PsubstsG (by rfl) _ hes (by row_entriesB), instOuter_subst_listToVec _ isSemiformula_Psubsts1G (by rfl) _ hes (by row_entriesB)]
  all_goals try row_entries_simpB
  row_finish

/-! ### `tshvNilCert` — `“x. …”`, `m = 1` -/

noncomputable def row_tshvNilCert_as : List V := []
noncomputable def row_tshvNilCert_c : V := subst LAct (listToVec [(𝟎 : V), (𝟎 : V), (𝟎 : V)]) PtshvG

theorem quote_row_tshvNilCert : (⌜Semiformula.lMap emb tshvNilCertB⌝ : V) = impChain LAct row_tshvNilCert_as row_tshvNilCert_c := by
  unfold tshvNilCertB row_tshvNilCert_as row_tshvNilCert_c PtshvG
  all_goals row_shapeB

lemma isSemiformula_tshvNilCert_c : IsSemiformula LAct ((1 : ℕ) : V) row_tshvNilCert_c := by
  unfold row_tshvNilCert_c
  exact isSemiformula_substRow isSemiformula_PtshvG _ (by rfl) (by row_entriesB)

/-- `tshvNilCert` at the witnesses `[wx]` (the DSL variables right-to-left). -/
lemma inst_tshvNilCert {wx : V} (hwx : IsSemiterm LAct 0 wx) :
    row_tshvNilCert_as.map (instOuter LAct [wx]) = [] ∧
    instOuter LAct [wx] row_tshvNilCert_c = tshvFact (𝟎 : V) (𝟎 : V) (𝟎 : V) := by
  have hes : ∀ e ∈ ([wx] : List V), IsSemiterm LAct 0 e := (List.forall_mem_cons.mpr ⟨hwx, List.forall_mem_nil _⟩)
  unfold row_tshvNilCert_as row_tshvNilCert_c
  simp only [List.map_cons, List.map_nil]
  rw [instOuter_subst_listToVec _ isSemiformula_PtshvG (by rfl) _ hes (by row_entriesB)]
  all_goals try row_entries_simpB
  row_finish

/-! ### `tshvAdjCert` — `“u' u t' t v' v k n. …”`, `m = 8` -/

noncomputable def row_tshvAdjCert_as : List V := [subst LAct (listToVec [bv 7, bv 3]) PtPi, subst LAct (listToVec [bv 6, bv 5]) PutvPi, subst LAct (listToVec [bv 2, bv 3]) PtshG, subst LAct (listToVec [bv 1, bv 6, bv 5]) PtshvG, subst LAct (listToVec [bv 4, bv 3, bv 5]) Padjoin, subst LAct (listToVec [bv 0, bv 2, bv 1]) Padjoin]
noncomputable def row_tshvAdjCert_c : V := subst LAct (listToVec [bv 0, (bv 6 ^+ (𝟏 : V)), bv 4]) PtshvG

theorem quote_row_tshvAdjCert : (⌜Semiformula.lMap emb tshvAdjCertB⌝ : V) = impChain LAct row_tshvAdjCert_as row_tshvAdjCert_c := by
  unfold tshvAdjCertB row_tshvAdjCert_as row_tshvAdjCert_c Padjoin PtPi PtshG PtshvG PutvPi
  all_goals row_shapeB

lemma isSemiformula_tshvAdjCert_c : IsSemiformula LAct ((8 : ℕ) : V) row_tshvAdjCert_c := by
  unfold row_tshvAdjCert_c
  exact isSemiformula_substRow isSemiformula_PtshvG _ (by rfl) (by row_entriesB)

/-- `tshvAdjCert` at the witnesses `[wn, wk, wv, wvp, wt, wtp, wu, wup]` (the DSL variables right-to-left). -/
lemma inst_tshvAdjCert {wn wk wv wvp wt wtp wu wup : V} (hwn : IsSemiterm LAct 0 wn) (hwk : IsSemiterm LAct 0 wk) (hwv : IsSemiterm LAct 0 wv) (hwvp : IsSemiterm LAct 0 wvp) (hwt : IsSemiterm LAct 0 wt) (hwtp : IsSemiterm LAct 0 wtp) (hwu : IsSemiterm LAct 0 wu) (hwup : IsSemiterm LAct 0 wup) :
    row_tshvAdjCert_as.map (instOuter LAct [wn, wk, wv, wvp, wt, wtp, wu, wup]) = [tPiFact wn wt, utvPiFact wk wv, tshFact wtp wt, tshvFact wu wk wv, adjFact wvp wt wv, adjFact wup wtp wu] ∧
    instOuter LAct [wn, wk, wv, wvp, wt, wtp, wu, wup] row_tshvAdjCert_c = tshvFact wup (wk ^+ (𝟏 : V)) wvp := by
  have hes : ∀ e ∈ ([wn, wk, wv, wvp, wt, wtp, wu, wup] : List V), IsSemiterm LAct 0 e := (List.forall_mem_cons.mpr ⟨hwn, List.forall_mem_cons.mpr ⟨hwk, List.forall_mem_cons.mpr ⟨hwv, List.forall_mem_cons.mpr ⟨hwvp, List.forall_mem_cons.mpr ⟨hwt, List.forall_mem_cons.mpr ⟨hwtp, List.forall_mem_cons.mpr ⟨hwu, List.forall_mem_cons.mpr ⟨hwup, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩)
  unfold row_tshvAdjCert_as row_tshvAdjCert_c
  simp only [List.map_cons, List.map_nil]
  rw [instOuter_subst_listToVec _ isSemiformula_PtPi (by rfl) _ hes (by row_entriesB), instOuter_subst_listToVec _ isSemiformula_PutvPi (by rfl) _ hes (by row_entriesB), instOuter_subst_listToVec _ isSemiformula_PtshG (by rfl) _ hes (by row_entriesB), instOuter_subst_listToVec _ isSemiformula_PtshvG (by rfl) _ hes (by row_entriesB), instOuter_subst_listToVec _ isSemiformula_Padjoin (by rfl) _ hes (by row_entriesB), instOuter_subst_listToVec _ isSemiformula_Padjoin (by rfl) _ hes (by row_entriesB), instOuter_subst_listToVec _ isSemiformula_PtshvG (by rfl) _ hes (by row_entriesB)]
  all_goals try row_entries_simpB
  row_finish

/-! ### `termShiftBvarCert` — `“t' t z. …”`, `m = 3` -/

noncomputable def row_termShiftBvarCert_as : List V := [subst LAct (listToVec [bv 1, bv 2]) Pbvar, subst LAct (listToVec [bv 0, bv 2]) Pbvar]
noncomputable def row_termShiftBvarCert_c : V := subst LAct (listToVec [bv 0, bv 1]) PtshG

theorem quote_row_termShiftBvarCert : (⌜Semiformula.lMap emb termShiftBvarCertB⌝ : V) = impChain LAct row_termShiftBvarCert_as row_termShiftBvarCert_c := by
  unfold termShiftBvarCertB row_termShiftBvarCert_as row_termShiftBvarCert_c Pbvar PtshG
  all_goals row_shapeB

lemma isSemiformula_termShiftBvarCert_c : IsSemiformula LAct ((3 : ℕ) : V) row_termShiftBvarCert_c := by
  unfold row_termShiftBvarCert_c
  exact isSemiformula_substRow isSemiformula_PtshG _ (by rfl) (by row_entriesB)

/-- `termShiftBvarCert` at the witnesses `[wz, wt, wtp]` (the DSL variables right-to-left). -/
lemma inst_termShiftBvarCert {wz wt wtp : V} (hwz : IsSemiterm LAct 0 wz) (hwt : IsSemiterm LAct 0 wt) (hwtp : IsSemiterm LAct 0 wtp) :
    row_termShiftBvarCert_as.map (instOuter LAct [wz, wt, wtp]) = [bvarFact wt wz, bvarFact wtp wz] ∧
    instOuter LAct [wz, wt, wtp] row_termShiftBvarCert_c = tshFact wtp wt := by
  have hes : ∀ e ∈ ([wz, wt, wtp] : List V), IsSemiterm LAct 0 e := (List.forall_mem_cons.mpr ⟨hwz, List.forall_mem_cons.mpr ⟨hwt, List.forall_mem_cons.mpr ⟨hwtp, List.forall_mem_nil _⟩⟩⟩)
  unfold row_termShiftBvarCert_as row_termShiftBvarCert_c
  simp only [List.map_cons, List.map_nil]
  rw [instOuter_subst_listToVec _ isSemiformula_Pbvar (by rfl) _ hes (by row_entriesB), instOuter_subst_listToVec _ isSemiformula_Pbvar (by rfl) _ hes (by row_entriesB), instOuter_subst_listToVec _ isSemiformula_PtshG (by rfl) _ hes (by row_entriesB)]
  all_goals try row_entries_simpB
  row_finish

/-! ### `termShiftFvarCert` — `“t' t x. …”`, `m = 3` -/

noncomputable def row_termShiftFvarCert_as : List V := [subst LAct (listToVec [bv 1, bv 2]) Pfvar, subst LAct (listToVec [bv 0, (bv 2 ^+ (𝟏 : V))]) Pfvar]
noncomputable def row_termShiftFvarCert_c : V := subst LAct (listToVec [bv 0, bv 1]) PtshG

theorem quote_row_termShiftFvarCert : (⌜Semiformula.lMap emb termShiftFvarCertB⌝ : V) = impChain LAct row_termShiftFvarCert_as row_termShiftFvarCert_c := by
  unfold termShiftFvarCertB row_termShiftFvarCert_as row_termShiftFvarCert_c Pfvar PtshG
  all_goals row_shapeB

lemma isSemiformula_termShiftFvarCert_c : IsSemiformula LAct ((3 : ℕ) : V) row_termShiftFvarCert_c := by
  unfold row_termShiftFvarCert_c
  exact isSemiformula_substRow isSemiformula_PtshG _ (by rfl) (by row_entriesB)

/-- `termShiftFvarCert` at the witnesses `[wx, wt, wtp]` (the DSL variables right-to-left). -/
lemma inst_termShiftFvarCert {wx wt wtp : V} (hwx : IsSemiterm LAct 0 wx) (hwt : IsSemiterm LAct 0 wt) (hwtp : IsSemiterm LAct 0 wtp) :
    row_termShiftFvarCert_as.map (instOuter LAct [wx, wt, wtp]) = [fvarFact wt wx, fvarFact wtp (wx ^+ (𝟏 : V))] ∧
    instOuter LAct [wx, wt, wtp] row_termShiftFvarCert_c = tshFact wtp wt := by
  have hes : ∀ e ∈ ([wx, wt, wtp] : List V), IsSemiterm LAct 0 e := (List.forall_mem_cons.mpr ⟨hwx, List.forall_mem_cons.mpr ⟨hwt, List.forall_mem_cons.mpr ⟨hwtp, List.forall_mem_nil _⟩⟩⟩)
  unfold row_termShiftFvarCert_as row_termShiftFvarCert_c
  simp only [List.map_cons, List.map_nil]
  rw [instOuter_subst_listToVec _ isSemiformula_Pfvar (by rfl) _ hes (by row_entriesB), instOuter_subst_listToVec _ isSemiformula_Pfvar (by rfl) _ hes (by row_entriesB), instOuter_subst_listToVec _ isSemiformula_PtshG (by rfl) _ hes (by row_entriesB)]
  all_goals try row_entries_simpB
  row_finish

/-! ### `termShiftFuncCert` — `“t' u v f k t. …”`, `m = 6` -/

noncomputable def row_termShiftFuncCert_as : List V := [subst LAct (listToVec [bv 4, bv 3]) PisFunc, subst LAct (listToVec [bv 4, bv 2]) PutvPi, subst LAct (listToVec [bv 5, bv 4, bv 3, bv 2]) Pfunc, subst LAct (listToVec [bv 1, bv 4, bv 2]) PtshvG, subst LAct (listToVec [bv 0, bv 4, bv 3, bv 1]) Pfunc]
noncomputable def row_termShiftFuncCert_c : V := subst LAct (listToVec [bv 0, bv 5]) PtshG

theorem quote_row_termShiftFuncCert : (⌜Semiformula.lMap emb termShiftFuncCertB⌝ : V) = impChain LAct row_termShiftFuncCert_as row_termShiftFuncCert_c := by
  unfold termShiftFuncCertB row_termShiftFuncCert_as row_termShiftFuncCert_c Pfunc PisFunc PtshG PtshvG PutvPi
  all_goals row_shapeB

lemma isSemiformula_termShiftFuncCert_c : IsSemiformula LAct ((6 : ℕ) : V) row_termShiftFuncCert_c := by
  unfold row_termShiftFuncCert_c
  exact isSemiformula_substRow isSemiformula_PtshG _ (by rfl) (by row_entriesB)

/-- `termShiftFuncCert` at the witnesses `[wt, wk, wf, wv, wu, wtp]` (the DSL variables right-to-left). -/
lemma inst_termShiftFuncCert {wt wk wf wv wu wtp : V} (hwt : IsSemiterm LAct 0 wt) (hwk : IsSemiterm LAct 0 wk) (hwf : IsSemiterm LAct 0 wf) (hwv : IsSemiterm LAct 0 wv) (hwu : IsSemiterm LAct 0 wu) (hwtp : IsSemiterm LAct 0 wtp) :
    row_termShiftFuncCert_as.map (instOuter LAct [wt, wk, wf, wv, wu, wtp]) = [isFuncFact wk wf, utvPiFact wk wv, funcFact wt wk wf wv, tshvFact wu wk wv, funcFact wtp wk wf wu] ∧
    instOuter LAct [wt, wk, wf, wv, wu, wtp] row_termShiftFuncCert_c = tshFact wtp wt := by
  have hes : ∀ e ∈ ([wt, wk, wf, wv, wu, wtp] : List V), IsSemiterm LAct 0 e := (List.forall_mem_cons.mpr ⟨hwt, List.forall_mem_cons.mpr ⟨hwk, List.forall_mem_cons.mpr ⟨hwf, List.forall_mem_cons.mpr ⟨hwv, List.forall_mem_cons.mpr ⟨hwu, List.forall_mem_cons.mpr ⟨hwtp, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩)
  unfold row_termShiftFuncCert_as row_termShiftFuncCert_c
  simp only [List.map_cons, List.map_nil]
  rw [instOuter_subst_listToVec _ isSemiformula_PisFunc (by rfl) _ hes (by row_entriesB), instOuter_subst_listToVec _ isSemiformula_PutvPi (by rfl) _ hes (by row_entriesB), instOuter_subst_listToVec _ isSemiformula_Pfunc (by rfl) _ hes (by row_entriesB), instOuter_subst_listToVec _ isSemiformula_PtshvG (by rfl) _ hes (by row_entriesB), instOuter_subst_listToVec _ isSemiformula_Pfunc (by rfl) _ hes (by row_entriesB), instOuter_subst_listToVec _ isSemiformula_PtshG (by rfl) _ hes (by row_entriesB)]
  all_goals try row_entries_simpB
  row_finish

/-! ### `tsvNilCert` — `“w. …”`, `m = 1` -/

noncomputable def row_tsvNilCert_as : List V := []
noncomputable def row_tsvNilCert_c : V := subst LAct (listToVec [(𝟎 : V), (𝟎 : V), bv 0, (𝟎 : V)]) PtsvG

theorem quote_row_tsvNilCert : (⌜Semiformula.lMap emb tsvNilCertB⌝ : V) = impChain LAct row_tsvNilCert_as row_tsvNilCert_c := by
  unfold tsvNilCertB row_tsvNilCert_as row_tsvNilCert_c PtsvG
  all_goals row_shapeB

lemma isSemiformula_tsvNilCert_c : IsSemiformula LAct ((1 : ℕ) : V) row_tsvNilCert_c := by
  unfold row_tsvNilCert_c
  exact isSemiformula_substRow isSemiformula_PtsvG _ (by rfl) (by row_entriesB)

/-- `tsvNilCert` at the witnesses `[ww]` (the DSL variables right-to-left). -/
lemma inst_tsvNilCert {ww : V} (hww : IsSemiterm LAct 0 ww) :
    row_tsvNilCert_as.map (instOuter LAct [ww]) = [] ∧
    instOuter LAct [ww] row_tsvNilCert_c = tsvFact (𝟎 : V) (𝟎 : V) ww (𝟎 : V) := by
  have hes : ∀ e ∈ ([ww] : List V), IsSemiterm LAct 0 e := (List.forall_mem_cons.mpr ⟨hww, List.forall_mem_nil _⟩)
  unfold row_tsvNilCert_as row_tsvNilCert_c
  simp only [List.map_cons, List.map_nil]
  rw [instOuter_subst_listToVec _ isSemiformula_PtsvG (by rfl) _ hes (by row_entriesB)]
  all_goals try row_entries_simpB
  row_finish

/-! ### `tsvAdjCert` — `“u' u e t v' v w k n. …”`, `m = 9` -/

noncomputable def row_tsvAdjCert_as : List V := [subst LAct (listToVec [bv 8, bv 3]) PtPi, subst LAct (listToVec [bv 7, bv 5]) PutvPi, subst LAct (listToVec [bv 2, bv 6, bv 3]) PtsG, subst LAct (listToVec [bv 1, bv 7, bv 6, bv 5]) PtsvG, subst LAct (listToVec [bv 4, bv 3, bv 5]) Padjoin, subst LAct (listToVec [bv 0, bv 2, bv 1]) Padjoin]
noncomputable def row_tsvAdjCert_c : V := subst LAct (listToVec [bv 0, (bv 7 ^+ (𝟏 : V)), bv 6, bv 4]) PtsvG

theorem quote_row_tsvAdjCert : (⌜Semiformula.lMap emb tsvAdjCertB⌝ : V) = impChain LAct row_tsvAdjCert_as row_tsvAdjCert_c := by
  unfold tsvAdjCertB row_tsvAdjCert_as row_tsvAdjCert_c Padjoin PtPi PtsG PtsvG PutvPi
  all_goals row_shapeB

lemma isSemiformula_tsvAdjCert_c : IsSemiformula LAct ((9 : ℕ) : V) row_tsvAdjCert_c := by
  unfold row_tsvAdjCert_c
  exact isSemiformula_substRow isSemiformula_PtsvG _ (by rfl) (by row_entriesB)

/-- `tsvAdjCert` at the witnesses `[wn, wk, ww, wv, wvp, wt, we, wu, wup]` (the DSL variables right-to-left). -/
lemma inst_tsvAdjCert {wn wk ww wv wvp wt we wu wup : V} (hwn : IsSemiterm LAct 0 wn) (hwk : IsSemiterm LAct 0 wk) (hww : IsSemiterm LAct 0 ww) (hwv : IsSemiterm LAct 0 wv) (hwvp : IsSemiterm LAct 0 wvp) (hwt : IsSemiterm LAct 0 wt) (hwe : IsSemiterm LAct 0 we) (hwu : IsSemiterm LAct 0 wu) (hwup : IsSemiterm LAct 0 wup) :
    row_tsvAdjCert_as.map (instOuter LAct [wn, wk, ww, wv, wvp, wt, we, wu, wup]) = [tPiFact wn wt, utvPiFact wk wv, tsFact we ww wt, tsvFact wu wk ww wv, adjFact wvp wt wv, adjFact wup we wu] ∧
    instOuter LAct [wn, wk, ww, wv, wvp, wt, we, wu, wup] row_tsvAdjCert_c = tsvFact wup (wk ^+ (𝟏 : V)) ww wvp := by
  have hes : ∀ e ∈ ([wn, wk, ww, wv, wvp, wt, we, wu, wup] : List V), IsSemiterm LAct 0 e := (List.forall_mem_cons.mpr ⟨hwn, List.forall_mem_cons.mpr ⟨hwk, List.forall_mem_cons.mpr ⟨hww, List.forall_mem_cons.mpr ⟨hwv, List.forall_mem_cons.mpr ⟨hwvp, List.forall_mem_cons.mpr ⟨hwt, List.forall_mem_cons.mpr ⟨hwe, List.forall_mem_cons.mpr ⟨hwu, List.forall_mem_cons.mpr ⟨hwup, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩)
  unfold row_tsvAdjCert_as row_tsvAdjCert_c
  simp only [List.map_cons, List.map_nil]
  rw [instOuter_subst_listToVec _ isSemiformula_PtPi (by rfl) _ hes (by row_entriesB), instOuter_subst_listToVec _ isSemiformula_PutvPi (by rfl) _ hes (by row_entriesB), instOuter_subst_listToVec _ isSemiformula_PtsG (by rfl) _ hes (by row_entriesB), instOuter_subst_listToVec _ isSemiformula_PtsvG (by rfl) _ hes (by row_entriesB), instOuter_subst_listToVec _ isSemiformula_Padjoin (by rfl) _ hes (by row_entriesB), instOuter_subst_listToVec _ isSemiformula_Padjoin (by rfl) _ hes (by row_entriesB), instOuter_subst_listToVec _ isSemiformula_PtsvG (by rfl) _ hes (by row_entriesB)]
  all_goals try row_entries_simpB
  row_finish

/-! ### `termSubstBvarCert` — `“e w z t. …”`, `m = 4` -/

noncomputable def row_termSubstBvarCert_as : List V := [subst LAct (listToVec [bv 3, bv 2]) Pbvar, subst LAct (listToVec [bv 0, bv 1, bv 2]) Pnth]
noncomputable def row_termSubstBvarCert_c : V := subst LAct (listToVec [bv 0, bv 1, bv 3]) PtsG

theorem quote_row_termSubstBvarCert : (⌜Semiformula.lMap emb termSubstBvarCertB⌝ : V) = impChain LAct row_termSubstBvarCert_as row_termSubstBvarCert_c := by
  unfold termSubstBvarCertB row_termSubstBvarCert_as row_termSubstBvarCert_c Pbvar Pnth PtsG
  all_goals row_shapeB

lemma isSemiformula_termSubstBvarCert_c : IsSemiformula LAct ((4 : ℕ) : V) row_termSubstBvarCert_c := by
  unfold row_termSubstBvarCert_c
  exact isSemiformula_substRow isSemiformula_PtsG _ (by rfl) (by row_entriesB)

/-- `termSubstBvarCert` at the witnesses `[wt, wz, ww, we]` (the DSL variables right-to-left). -/
lemma inst_termSubstBvarCert {wt wz ww we : V} (hwt : IsSemiterm LAct 0 wt) (hwz : IsSemiterm LAct 0 wz) (hww : IsSemiterm LAct 0 ww) (hwe : IsSemiterm LAct 0 we) :
    row_termSubstBvarCert_as.map (instOuter LAct [wt, wz, ww, we]) = [bvarFact wt wz, nthFact we ww wz] ∧
    instOuter LAct [wt, wz, ww, we] row_termSubstBvarCert_c = tsFact we ww wt := by
  have hes : ∀ e ∈ ([wt, wz, ww, we] : List V), IsSemiterm LAct 0 e := (List.forall_mem_cons.mpr ⟨hwt, List.forall_mem_cons.mpr ⟨hwz, List.forall_mem_cons.mpr ⟨hww, List.forall_mem_cons.mpr ⟨hwe, List.forall_mem_nil _⟩⟩⟩⟩)
  unfold row_termSubstBvarCert_as row_termSubstBvarCert_c
  simp only [List.map_cons, List.map_nil]
  rw [instOuter_subst_listToVec _ isSemiformula_Pbvar (by rfl) _ hes (by row_entriesB), instOuter_subst_listToVec _ isSemiformula_Pnth (by rfl) _ hes (by row_entriesB), instOuter_subst_listToVec _ isSemiformula_PtsG (by rfl) _ hes (by row_entriesB)]
  all_goals try row_entries_simpB
  row_finish

/-! ### `termSubstFvarCert` — `“e w x t. …”`, `m = 4` -/

noncomputable def row_termSubstFvarCert_as : List V := [subst LAct (listToVec [bv 3, bv 2]) Pfvar, subst LAct (listToVec [bv 0, bv 2]) Pfvar]
noncomputable def row_termSubstFvarCert_c : V := subst LAct (listToVec [bv 0, bv 1, bv 3]) PtsG

theorem quote_row_termSubstFvarCert : (⌜Semiformula.lMap emb termSubstFvarCertB⌝ : V) = impChain LAct row_termSubstFvarCert_as row_termSubstFvarCert_c := by
  unfold termSubstFvarCertB row_termSubstFvarCert_as row_termSubstFvarCert_c Pfvar PtsG
  all_goals row_shapeB

lemma isSemiformula_termSubstFvarCert_c : IsSemiformula LAct ((4 : ℕ) : V) row_termSubstFvarCert_c := by
  unfold row_termSubstFvarCert_c
  exact isSemiformula_substRow isSemiformula_PtsG _ (by rfl) (by row_entriesB)

/-- `termSubstFvarCert` at the witnesses `[wt, wx, ww, we]` (the DSL variables right-to-left). -/
lemma inst_termSubstFvarCert {wt wx ww we : V} (hwt : IsSemiterm LAct 0 wt) (hwx : IsSemiterm LAct 0 wx) (hww : IsSemiterm LAct 0 ww) (hwe : IsSemiterm LAct 0 we) :
    row_termSubstFvarCert_as.map (instOuter LAct [wt, wx, ww, we]) = [fvarFact wt wx, fvarFact we wx] ∧
    instOuter LAct [wt, wx, ww, we] row_termSubstFvarCert_c = tsFact we ww wt := by
  have hes : ∀ e ∈ ([wt, wx, ww, we] : List V), IsSemiterm LAct 0 e := (List.forall_mem_cons.mpr ⟨hwt, List.forall_mem_cons.mpr ⟨hwx, List.forall_mem_cons.mpr ⟨hww, List.forall_mem_cons.mpr ⟨hwe, List.forall_mem_nil _⟩⟩⟩⟩)
  unfold row_termSubstFvarCert_as row_termSubstFvarCert_c
  simp only [List.map_cons, List.map_nil]
  rw [instOuter_subst_listToVec _ isSemiformula_Pfvar (by rfl) _ hes (by row_entriesB), instOuter_subst_listToVec _ isSemiformula_Pfvar (by rfl) _ hes (by row_entriesB), instOuter_subst_listToVec _ isSemiformula_PtsG (by rfl) _ hes (by row_entriesB)]
  all_goals try row_entries_simpB
  row_finish

/-! ### `termSubstFuncCert` — `“e u v f k t w. …”`, `m = 7` -/

noncomputable def row_termSubstFuncCert_as : List V := [subst LAct (listToVec [bv 4, bv 3]) PisFunc, subst LAct (listToVec [bv 4, bv 2]) PutvPi, subst LAct (listToVec [bv 5, bv 4, bv 3, bv 2]) Pfunc, subst LAct (listToVec [bv 1, bv 4, bv 6, bv 2]) PtsvG, subst LAct (listToVec [bv 0, bv 4, bv 3, bv 1]) Pfunc]
noncomputable def row_termSubstFuncCert_c : V := subst LAct (listToVec [bv 0, bv 6, bv 5]) PtsG

theorem quote_row_termSubstFuncCert : (⌜Semiformula.lMap emb termSubstFuncCertB⌝ : V) = impChain LAct row_termSubstFuncCert_as row_termSubstFuncCert_c := by
  unfold termSubstFuncCertB row_termSubstFuncCert_as row_termSubstFuncCert_c Pfunc PisFunc PtsG PtsvG PutvPi
  all_goals row_shapeB

lemma isSemiformula_termSubstFuncCert_c : IsSemiformula LAct ((7 : ℕ) : V) row_termSubstFuncCert_c := by
  unfold row_termSubstFuncCert_c
  exact isSemiformula_substRow isSemiformula_PtsG _ (by rfl) (by row_entriesB)

/-- `termSubstFuncCert` at the witnesses `[ww, wt, wk, wf, wv, wu, we]` (the DSL variables right-to-left). -/
lemma inst_termSubstFuncCert {ww wt wk wf wv wu we : V} (hww : IsSemiterm LAct 0 ww) (hwt : IsSemiterm LAct 0 wt) (hwk : IsSemiterm LAct 0 wk) (hwf : IsSemiterm LAct 0 wf) (hwv : IsSemiterm LAct 0 wv) (hwu : IsSemiterm LAct 0 wu) (hwe : IsSemiterm LAct 0 we) :
    row_termSubstFuncCert_as.map (instOuter LAct [ww, wt, wk, wf, wv, wu, we]) = [isFuncFact wk wf, utvPiFact wk wv, funcFact wt wk wf wv, tsvFact wu wk ww wv, funcFact we wk wf wu] ∧
    instOuter LAct [ww, wt, wk, wf, wv, wu, we] row_termSubstFuncCert_c = tsFact we ww wt := by
  have hes : ∀ e ∈ ([ww, wt, wk, wf, wv, wu, we] : List V), IsSemiterm LAct 0 e := (List.forall_mem_cons.mpr ⟨hww, List.forall_mem_cons.mpr ⟨hwt, List.forall_mem_cons.mpr ⟨hwk, List.forall_mem_cons.mpr ⟨hwf, List.forall_mem_cons.mpr ⟨hwv, List.forall_mem_cons.mpr ⟨hwu, List.forall_mem_cons.mpr ⟨hwe, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩)
  unfold row_termSubstFuncCert_as row_termSubstFuncCert_c
  simp only [List.map_cons, List.map_nil]
  rw [instOuter_subst_listToVec _ isSemiformula_PisFunc (by rfl) _ hes (by row_entriesB), instOuter_subst_listToVec _ isSemiformula_PutvPi (by rfl) _ hes (by row_entriesB), instOuter_subst_listToVec _ isSemiformula_Pfunc (by rfl) _ hes (by row_entriesB), instOuter_subst_listToVec _ isSemiformula_PtsvG (by rfl) _ hes (by row_entriesB), instOuter_subst_listToVec _ isSemiformula_Pfunc (by rfl) _ hes (by row_entriesB), instOuter_subst_listToVec _ isSemiformula_PtsG (by rfl) _ hes (by row_entriesB)]
  all_goals try row_entries_simpB
  row_finish

/-! ### `tbshvNilCert` — `“x. …”`, `m = 1` -/

noncomputable def row_tbshvNilCert_as : List V := []
noncomputable def row_tbshvNilCert_c : V := subst LAct (listToVec [(𝟎 : V), (𝟎 : V), (𝟎 : V)]) PtbshvG

theorem quote_row_tbshvNilCert : (⌜Semiformula.lMap emb tbshvNilCertB⌝ : V) = impChain LAct row_tbshvNilCert_as row_tbshvNilCert_c := by
  unfold tbshvNilCertB row_tbshvNilCert_as row_tbshvNilCert_c PtbshvG
  all_goals row_shapeB

lemma isSemiformula_tbshvNilCert_c : IsSemiformula LAct ((1 : ℕ) : V) row_tbshvNilCert_c := by
  unfold row_tbshvNilCert_c
  exact isSemiformula_substRow isSemiformula_PtbshvG _ (by rfl) (by row_entriesB)

/-- `tbshvNilCert` at the witnesses `[wx]` (the DSL variables right-to-left). -/
lemma inst_tbshvNilCert {wx : V} (hwx : IsSemiterm LAct 0 wx) :
    row_tbshvNilCert_as.map (instOuter LAct [wx]) = [] ∧
    instOuter LAct [wx] row_tbshvNilCert_c = tbshvFact (𝟎 : V) (𝟎 : V) (𝟎 : V) := by
  have hes : ∀ e ∈ ([wx] : List V), IsSemiterm LAct 0 e := (List.forall_mem_cons.mpr ⟨hwx, List.forall_mem_nil _⟩)
  unfold row_tbshvNilCert_as row_tbshvNilCert_c
  simp only [List.map_cons, List.map_nil]
  rw [instOuter_subst_listToVec _ isSemiformula_PtbshvG (by rfl) _ hes (by row_entriesB)]
  all_goals try row_entries_simpB
  row_finish

/-! ### `tbshvAdjCert` — `“u' u t' t v' v k n. …”`, `m = 8` -/

noncomputable def row_tbshvAdjCert_as : List V := [subst LAct (listToVec [bv 7, bv 3]) PtPi, subst LAct (listToVec [bv 6, bv 5]) PutvPi, subst LAct (listToVec [bv 2, bv 3]) PtbshG, subst LAct (listToVec [bv 1, bv 6, bv 5]) PtbshvG, subst LAct (listToVec [bv 4, bv 3, bv 5]) Padjoin, subst LAct (listToVec [bv 0, bv 2, bv 1]) Padjoin]
noncomputable def row_tbshvAdjCert_c : V := subst LAct (listToVec [bv 0, (bv 6 ^+ (𝟏 : V)), bv 4]) PtbshvG

theorem quote_row_tbshvAdjCert : (⌜Semiformula.lMap emb tbshvAdjCertB⌝ : V) = impChain LAct row_tbshvAdjCert_as row_tbshvAdjCert_c := by
  unfold tbshvAdjCertB row_tbshvAdjCert_as row_tbshvAdjCert_c Padjoin PtPi PtbshG PtbshvG PutvPi
  all_goals row_shapeB

lemma isSemiformula_tbshvAdjCert_c : IsSemiformula LAct ((8 : ℕ) : V) row_tbshvAdjCert_c := by
  unfold row_tbshvAdjCert_c
  exact isSemiformula_substRow isSemiformula_PtbshvG _ (by rfl) (by row_entriesB)

/-- `tbshvAdjCert` at the witnesses `[wn, wk, wv, wvp, wt, wtp, wu, wup]` (the DSL variables right-to-left). -/
lemma inst_tbshvAdjCert {wn wk wv wvp wt wtp wu wup : V} (hwn : IsSemiterm LAct 0 wn) (hwk : IsSemiterm LAct 0 wk) (hwv : IsSemiterm LAct 0 wv) (hwvp : IsSemiterm LAct 0 wvp) (hwt : IsSemiterm LAct 0 wt) (hwtp : IsSemiterm LAct 0 wtp) (hwu : IsSemiterm LAct 0 wu) (hwup : IsSemiterm LAct 0 wup) :
    row_tbshvAdjCert_as.map (instOuter LAct [wn, wk, wv, wvp, wt, wtp, wu, wup]) = [tPiFact wn wt, utvPiFact wk wv, tbshFact wtp wt, tbshvFact wu wk wv, adjFact wvp wt wv, adjFact wup wtp wu] ∧
    instOuter LAct [wn, wk, wv, wvp, wt, wtp, wu, wup] row_tbshvAdjCert_c = tbshvFact wup (wk ^+ (𝟏 : V)) wvp := by
  have hes : ∀ e ∈ ([wn, wk, wv, wvp, wt, wtp, wu, wup] : List V), IsSemiterm LAct 0 e := (List.forall_mem_cons.mpr ⟨hwn, List.forall_mem_cons.mpr ⟨hwk, List.forall_mem_cons.mpr ⟨hwv, List.forall_mem_cons.mpr ⟨hwvp, List.forall_mem_cons.mpr ⟨hwt, List.forall_mem_cons.mpr ⟨hwtp, List.forall_mem_cons.mpr ⟨hwu, List.forall_mem_cons.mpr ⟨hwup, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩)
  unfold row_tbshvAdjCert_as row_tbshvAdjCert_c
  simp only [List.map_cons, List.map_nil]
  rw [instOuter_subst_listToVec _ isSemiformula_PtPi (by rfl) _ hes (by row_entriesB), instOuter_subst_listToVec _ isSemiformula_PutvPi (by rfl) _ hes (by row_entriesB), instOuter_subst_listToVec _ isSemiformula_PtbshG (by rfl) _ hes (by row_entriesB), instOuter_subst_listToVec _ isSemiformula_PtbshvG (by rfl) _ hes (by row_entriesB), instOuter_subst_listToVec _ isSemiformula_Padjoin (by rfl) _ hes (by row_entriesB), instOuter_subst_listToVec _ isSemiformula_Padjoin (by rfl) _ hes (by row_entriesB), instOuter_subst_listToVec _ isSemiformula_PtbshvG (by rfl) _ hes (by row_entriesB)]
  all_goals try row_entries_simpB
  row_finish

/-! ### `termBShiftBvarCert` — `“t' t z. …”`, `m = 3` -/

noncomputable def row_termBShiftBvarCert_as : List V := [subst LAct (listToVec [bv 1, bv 2]) Pbvar, subst LAct (listToVec [bv 0, (bv 2 ^+ (𝟏 : V))]) Pbvar]
noncomputable def row_termBShiftBvarCert_c : V := subst LAct (listToVec [bv 0, bv 1]) PtbshG

theorem quote_row_termBShiftBvarCert : (⌜Semiformula.lMap emb termBShiftBvarCertB⌝ : V) = impChain LAct row_termBShiftBvarCert_as row_termBShiftBvarCert_c := by
  unfold termBShiftBvarCertB row_termBShiftBvarCert_as row_termBShiftBvarCert_c Pbvar PtbshG
  all_goals row_shapeB

lemma isSemiformula_termBShiftBvarCert_c : IsSemiformula LAct ((3 : ℕ) : V) row_termBShiftBvarCert_c := by
  unfold row_termBShiftBvarCert_c
  exact isSemiformula_substRow isSemiformula_PtbshG _ (by rfl) (by row_entriesB)

/-- `termBShiftBvarCert` at the witnesses `[wz, wt, wtp]` (the DSL variables right-to-left). -/
lemma inst_termBShiftBvarCert {wz wt wtp : V} (hwz : IsSemiterm LAct 0 wz) (hwt : IsSemiterm LAct 0 wt) (hwtp : IsSemiterm LAct 0 wtp) :
    row_termBShiftBvarCert_as.map (instOuter LAct [wz, wt, wtp]) = [bvarFact wt wz, bvarFact wtp (wz ^+ (𝟏 : V))] ∧
    instOuter LAct [wz, wt, wtp] row_termBShiftBvarCert_c = tbshFact wtp wt := by
  have hes : ∀ e ∈ ([wz, wt, wtp] : List V), IsSemiterm LAct 0 e := (List.forall_mem_cons.mpr ⟨hwz, List.forall_mem_cons.mpr ⟨hwt, List.forall_mem_cons.mpr ⟨hwtp, List.forall_mem_nil _⟩⟩⟩)
  unfold row_termBShiftBvarCert_as row_termBShiftBvarCert_c
  simp only [List.map_cons, List.map_nil]
  rw [instOuter_subst_listToVec _ isSemiformula_Pbvar (by rfl) _ hes (by row_entriesB), instOuter_subst_listToVec _ isSemiformula_Pbvar (by rfl) _ hes (by row_entriesB), instOuter_subst_listToVec _ isSemiformula_PtbshG (by rfl) _ hes (by row_entriesB)]
  all_goals try row_entries_simpB
  row_finish

/-! ### `termBShiftFvarCert` — `“t' t x. …”`, `m = 3` -/

noncomputable def row_termBShiftFvarCert_as : List V := [subst LAct (listToVec [bv 1, bv 2]) Pfvar, subst LAct (listToVec [bv 0, bv 2]) Pfvar]
noncomputable def row_termBShiftFvarCert_c : V := subst LAct (listToVec [bv 0, bv 1]) PtbshG

theorem quote_row_termBShiftFvarCert : (⌜Semiformula.lMap emb termBShiftFvarCertB⌝ : V) = impChain LAct row_termBShiftFvarCert_as row_termBShiftFvarCert_c := by
  unfold termBShiftFvarCertB row_termBShiftFvarCert_as row_termBShiftFvarCert_c Pfvar PtbshG
  all_goals row_shapeB

lemma isSemiformula_termBShiftFvarCert_c : IsSemiformula LAct ((3 : ℕ) : V) row_termBShiftFvarCert_c := by
  unfold row_termBShiftFvarCert_c
  exact isSemiformula_substRow isSemiformula_PtbshG _ (by rfl) (by row_entriesB)

/-- `termBShiftFvarCert` at the witnesses `[wx, wt, wtp]` (the DSL variables right-to-left). -/
lemma inst_termBShiftFvarCert {wx wt wtp : V} (hwx : IsSemiterm LAct 0 wx) (hwt : IsSemiterm LAct 0 wt) (hwtp : IsSemiterm LAct 0 wtp) :
    row_termBShiftFvarCert_as.map (instOuter LAct [wx, wt, wtp]) = [fvarFact wt wx, fvarFact wtp wx] ∧
    instOuter LAct [wx, wt, wtp] row_termBShiftFvarCert_c = tbshFact wtp wt := by
  have hes : ∀ e ∈ ([wx, wt, wtp] : List V), IsSemiterm LAct 0 e := (List.forall_mem_cons.mpr ⟨hwx, List.forall_mem_cons.mpr ⟨hwt, List.forall_mem_cons.mpr ⟨hwtp, List.forall_mem_nil _⟩⟩⟩)
  unfold row_termBShiftFvarCert_as row_termBShiftFvarCert_c
  simp only [List.map_cons, List.map_nil]
  rw [instOuter_subst_listToVec _ isSemiformula_Pfvar (by rfl) _ hes (by row_entriesB), instOuter_subst_listToVec _ isSemiformula_Pfvar (by rfl) _ hes (by row_entriesB), instOuter_subst_listToVec _ isSemiformula_PtbshG (by rfl) _ hes (by row_entriesB)]
  all_goals try row_entries_simpB
  row_finish

/-! ### `termBShiftFuncCert` — `“t' u v f k t. …”`, `m = 6` -/

noncomputable def row_termBShiftFuncCert_as : List V := [subst LAct (listToVec [bv 4, bv 3]) PisFunc, subst LAct (listToVec [bv 4, bv 2]) PutvPi, subst LAct (listToVec [bv 5, bv 4, bv 3, bv 2]) Pfunc, subst LAct (listToVec [bv 1, bv 4, bv 2]) PtbshvG, subst LAct (listToVec [bv 0, bv 4, bv 3, bv 1]) Pfunc]
noncomputable def row_termBShiftFuncCert_c : V := subst LAct (listToVec [bv 0, bv 5]) PtbshG

theorem quote_row_termBShiftFuncCert : (⌜Semiformula.lMap emb termBShiftFuncCertB⌝ : V) = impChain LAct row_termBShiftFuncCert_as row_termBShiftFuncCert_c := by
  unfold termBShiftFuncCertB row_termBShiftFuncCert_as row_termBShiftFuncCert_c Pfunc PisFunc PtbshG PtbshvG PutvPi
  all_goals row_shapeB

lemma isSemiformula_termBShiftFuncCert_c : IsSemiformula LAct ((6 : ℕ) : V) row_termBShiftFuncCert_c := by
  unfold row_termBShiftFuncCert_c
  exact isSemiformula_substRow isSemiformula_PtbshG _ (by rfl) (by row_entriesB)

/-- `termBShiftFuncCert` at the witnesses `[wt, wk, wf, wv, wu, wtp]` (the DSL variables right-to-left). -/
lemma inst_termBShiftFuncCert {wt wk wf wv wu wtp : V} (hwt : IsSemiterm LAct 0 wt) (hwk : IsSemiterm LAct 0 wk) (hwf : IsSemiterm LAct 0 wf) (hwv : IsSemiterm LAct 0 wv) (hwu : IsSemiterm LAct 0 wu) (hwtp : IsSemiterm LAct 0 wtp) :
    row_termBShiftFuncCert_as.map (instOuter LAct [wt, wk, wf, wv, wu, wtp]) = [isFuncFact wk wf, utvPiFact wk wv, funcFact wt wk wf wv, tbshvFact wu wk wv, funcFact wtp wk wf wu] ∧
    instOuter LAct [wt, wk, wf, wv, wu, wtp] row_termBShiftFuncCert_c = tbshFact wtp wt := by
  have hes : ∀ e ∈ ([wt, wk, wf, wv, wu, wtp] : List V), IsSemiterm LAct 0 e := (List.forall_mem_cons.mpr ⟨hwt, List.forall_mem_cons.mpr ⟨hwk, List.forall_mem_cons.mpr ⟨hwf, List.forall_mem_cons.mpr ⟨hwv, List.forall_mem_cons.mpr ⟨hwu, List.forall_mem_cons.mpr ⟨hwtp, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩)
  unfold row_termBShiftFuncCert_as row_termBShiftFuncCert_c
  simp only [List.map_cons, List.map_nil]
  rw [instOuter_subst_listToVec _ isSemiformula_PisFunc (by rfl) _ hes (by row_entriesB), instOuter_subst_listToVec _ isSemiformula_PutvPi (by rfl) _ hes (by row_entriesB), instOuter_subst_listToVec _ isSemiformula_Pfunc (by rfl) _ hes (by row_entriesB), instOuter_subst_listToVec _ isSemiformula_PtbshvG (by rfl) _ hes (by row_entriesB), instOuter_subst_listToVec _ isSemiformula_Pfunc (by rfl) _ hes (by row_entriesB), instOuter_subst_listToVec _ isSemiformula_PtbshG (by rfl) _ hes (by row_entriesB)]
  all_goals try row_entries_simpB
  row_finish

/-! ### `qVecCert` — `“u sw z w k. …”`, `m = 5` -/

noncomputable def row_qVecCert_as : List V := [subst LAct (listToVec [bv 4, bv 3]) PutvPi, subst LAct (listToVec [bv 1, bv 4, bv 3]) PtbshvG, subst LAct (listToVec [bv 2, (𝟎 : V)]) Pbvar, subst LAct (listToVec [bv 0, bv 2, bv 1]) Padjoin]
noncomputable def row_qVecCert_c : V := subst LAct (listToVec [bv 0, bv 3]) PqVecG

theorem quote_row_qVecCert : (⌜Semiformula.lMap emb qVecCertB⌝ : V) = impChain LAct row_qVecCert_as row_qVecCert_c := by
  unfold qVecCertB row_qVecCert_as row_qVecCert_c Padjoin Pbvar PqVecG PtbshvG PutvPi
  all_goals row_shapeB

lemma isSemiformula_qVecCert_c : IsSemiformula LAct ((5 : ℕ) : V) row_qVecCert_c := by
  unfold row_qVecCert_c
  exact isSemiformula_substRow isSemiformula_PqVecG _ (by rfl) (by row_entriesB)

/-- `qVecCert` at the witnesses `[wk, ww, wz, wsw, wu]` (the DSL variables right-to-left). -/
lemma inst_qVecCert {wk ww wz wsw wu : V} (hwk : IsSemiterm LAct 0 wk) (hww : IsSemiterm LAct 0 ww) (hwz : IsSemiterm LAct 0 wz) (hwsw : IsSemiterm LAct 0 wsw) (hwu : IsSemiterm LAct 0 wu) :
    row_qVecCert_as.map (instOuter LAct [wk, ww, wz, wsw, wu]) = [utvPiFact wk ww, tbshvFact wsw wk ww, bvarFact wz (𝟎 : V), adjFact wu wz wsw] ∧
    instOuter LAct [wk, ww, wz, wsw, wu] row_qVecCert_c = qVecFact wu ww := by
  have hes : ∀ e ∈ ([wk, ww, wz, wsw, wu] : List V), IsSemiterm LAct 0 e := (List.forall_mem_cons.mpr ⟨hwk, List.forall_mem_cons.mpr ⟨hww, List.forall_mem_cons.mpr ⟨hwz, List.forall_mem_cons.mpr ⟨hwsw, List.forall_mem_cons.mpr ⟨hwu, List.forall_mem_nil _⟩⟩⟩⟩⟩)
  unfold row_qVecCert_as row_qVecCert_c
  simp only [List.map_cons, List.map_nil]
  rw [instOuter_subst_listToVec _ isSemiformula_PutvPi (by rfl) _ hes (by row_entriesB), instOuter_subst_listToVec _ isSemiformula_PtbshvG (by rfl) _ hes (by row_entriesB), instOuter_subst_listToVec _ isSemiformula_Pbvar (by rfl) _ hes (by row_entriesB), instOuter_subst_listToVec _ isSemiformula_Padjoin (by rfl) _ hes (by row_entriesB), instOuter_subst_listToVec _ isSemiformula_PqVecG (by rfl) _ hes (by row_entriesB)]
  all_goals try row_entries_simpB
  row_finish

/-! ### `qVecNth0` — `“u w. …”`, `m = 2` -/

noncomputable def row_qVecNth0_as : List V := [subst LAct (listToVec [bv 0, bv 1]) PqVecG]
noncomputable def row_qVecNth0_body : V := subst LAct (listToVec [bv 0, (𝟎 : V)]) Pbvar ^⋏ subst LAct (listToVec [bv 0, bv 1, (𝟎 : V)]) Pnth
noncomputable def row_qVecNth0_R : V := row_qVecNth0_body

lemma row_qVecNth0_R_eq : (row_qVecNth0_R : V) = exsIter 0 row_qVecNth0_body := rfl

/-! ### `qVecNthSucc` — `“e' e u w i k. …”`, `m = 6` -/

noncomputable def row_qVecNthSucc_as : List V := [subst LAct (listToVec [bv 5, bv 3]) PutvPi, subst LAct (listToVec [bv 4, bv 5]) Plt, subst LAct (listToVec [bv 2, bv 3]) PqVecG, subst LAct (listToVec [bv 1, bv 3, bv 4]) Pnth, subst LAct (listToVec [bv 0, bv 1]) PtbshG]
noncomputable def row_qVecNthSucc_c : V := subst LAct (listToVec [bv 0, bv 2, (bv 4 ^+ (𝟏 : V))]) Pnth

/-- `qVecNthSucc` at the witnesses `[wk, wi, ww, wu, we, wep]` (the DSL variables right-to-left). -/
lemma inst_qVecNthSucc {wk wi ww wu we wep : V} (hwk : IsSemiterm LAct 0 wk) (hwi : IsSemiterm LAct 0 wi) (hww : IsSemiterm LAct 0 ww) (hwu : IsSemiterm LAct 0 wu) (hwe : IsSemiterm LAct 0 we) (hwep : IsSemiterm LAct 0 wep) :
    row_qVecNthSucc_as.map (instOuter LAct [wk, wi, ww, wu, we, wep]) = [utvPiFact wk ww, ltFact wi wk, qVecFact wu ww, nthFact we ww wi, tbshFact wep we] ∧
    instOuter LAct [wk, wi, ww, wu, we, wep] row_qVecNthSucc_c = nthFact wep wu (wi ^+ (𝟏 : V)) := by
  have hes : ∀ e ∈ ([wk, wi, ww, wu, we, wep] : List V), IsSemiterm LAct 0 e := (List.forall_mem_cons.mpr ⟨hwk, List.forall_mem_cons.mpr ⟨hwi, List.forall_mem_cons.mpr ⟨hww, List.forall_mem_cons.mpr ⟨hwu, List.forall_mem_cons.mpr ⟨hwe, List.forall_mem_cons.mpr ⟨hwep, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩)
  unfold row_qVecNthSucc_as row_qVecNthSucc_c
  simp only [List.map_cons, List.map_nil]
  rw [instOuter_subst_listToVec _ isSemiformula_PutvPi (by rfl) _ hes (by row_entriesB), instOuter_subst_listToVec _ isSemiformula_Plt (by rfl) _ hes (by row_entriesB), instOuter_subst_listToVec _ isSemiformula_PqVecG (by rfl) _ hes (by row_entriesB), instOuter_subst_listToVec _ isSemiformula_Pnth (by rfl) _ hes (by row_entriesB), instOuter_subst_listToVec _ isSemiformula_PtbshG (by rfl) _ hes (by row_entriesB), instOuter_subst_listToVec _ isSemiformula_Pnth (by rfl) _ hes (by row_entriesB)]
  all_goals try row_entries_simpB
  row_finish

/-! ### `nthAdjoinZero` — `“w t v. …”`, `m = 3` -/

noncomputable def row_nthAdjoinZero_as : List V := [subst LAct (listToVec [bv 0, bv 1, bv 2]) Padjoin]
noncomputable def row_nthAdjoinZero_c : V := subst LAct (listToVec [bv 1, bv 0, (𝟎 : V)]) Pnth

theorem quote_row_nthAdjoinZero : (⌜Semiformula.lMap emb nthAdjoinZeroB⌝ : V) = impChain LAct row_nthAdjoinZero_as row_nthAdjoinZero_c := by
  unfold nthAdjoinZeroB row_nthAdjoinZero_as row_nthAdjoinZero_c Padjoin Pnth
  all_goals row_shapeB

lemma isSemiformula_nthAdjoinZero_c : IsSemiformula LAct ((3 : ℕ) : V) row_nthAdjoinZero_c := by
  unfold row_nthAdjoinZero_c
  exact isSemiformula_substRow isSemiformula_Pnth _ (by rfl) (by row_entriesB)

/-- `nthAdjoinZero` at the witnesses `[wv, wt, ww]` (the DSL variables right-to-left). -/
lemma inst_nthAdjoinZero {wv wt ww : V} (hwv : IsSemiterm LAct 0 wv) (hwt : IsSemiterm LAct 0 wt) (hww : IsSemiterm LAct 0 ww) :
    row_nthAdjoinZero_as.map (instOuter LAct [wv, wt, ww]) = [adjFact ww wt wv] ∧
    instOuter LAct [wv, wt, ww] row_nthAdjoinZero_c = nthFact wt ww (𝟎 : V) := by
  have hes : ∀ e ∈ ([wv, wt, ww] : List V), IsSemiterm LAct 0 e := (List.forall_mem_cons.mpr ⟨hwv, List.forall_mem_cons.mpr ⟨hwt, List.forall_mem_cons.mpr ⟨hww, List.forall_mem_nil _⟩⟩⟩)
  unfold row_nthAdjoinZero_as row_nthAdjoinZero_c
  simp only [List.map_cons, List.map_nil]
  rw [instOuter_subst_listToVec _ isSemiformula_Padjoin (by rfl) _ hes (by row_entriesB), instOuter_subst_listToVec _ isSemiformula_Pnth (by rfl) _ hes (by row_entriesB)]
  all_goals try row_entries_simpB
  row_finish

/-! ### `nthAdjoinSucc` — `“e w t v i. …”`, `m = 5` -/

noncomputable def row_nthAdjoinSucc_as : List V := [subst LAct (listToVec [bv 1, bv 2, bv 3]) Padjoin, subst LAct (listToVec [bv 0, bv 3, bv 4]) Pnth]
noncomputable def row_nthAdjoinSucc_c : V := subst LAct (listToVec [bv 0, bv 1, (bv 4 ^+ (𝟏 : V))]) Pnth

theorem quote_row_nthAdjoinSucc : (⌜Semiformula.lMap emb nthAdjoinSuccB⌝ : V) = impChain LAct row_nthAdjoinSucc_as row_nthAdjoinSucc_c := by
  unfold nthAdjoinSuccB row_nthAdjoinSucc_as row_nthAdjoinSucc_c Padjoin Pnth
  all_goals row_shapeB

lemma isSemiformula_nthAdjoinSucc_c : IsSemiformula LAct ((5 : ℕ) : V) row_nthAdjoinSucc_c := by
  unfold row_nthAdjoinSucc_c
  exact isSemiformula_substRow isSemiformula_Pnth _ (by rfl) (by row_entriesB)

/-- `nthAdjoinSucc` at the witnesses `[wi, wv, wt, ww, we]` (the DSL variables right-to-left). -/
lemma inst_nthAdjoinSucc {wi wv wt ww we : V} (hwi : IsSemiterm LAct 0 wi) (hwv : IsSemiterm LAct 0 wv) (hwt : IsSemiterm LAct 0 wt) (hww : IsSemiterm LAct 0 ww) (hwe : IsSemiterm LAct 0 we) :
    row_nthAdjoinSucc_as.map (instOuter LAct [wi, wv, wt, ww, we]) = [adjFact ww wt wv, nthFact we wv wi] ∧
    instOuter LAct [wi, wv, wt, ww, we] row_nthAdjoinSucc_c = nthFact we ww (wi ^+ (𝟏 : V)) := by
  have hes : ∀ e ∈ ([wi, wv, wt, ww, we] : List V), IsSemiterm LAct 0 e := (List.forall_mem_cons.mpr ⟨hwi, List.forall_mem_cons.mpr ⟨hwv, List.forall_mem_cons.mpr ⟨hwt, List.forall_mem_cons.mpr ⟨hww, List.forall_mem_cons.mpr ⟨hwe, List.forall_mem_nil _⟩⟩⟩⟩⟩)
  unfold row_nthAdjoinSucc_as row_nthAdjoinSucc_c
  simp only [List.map_cons, List.map_nil]
  rw [instOuter_subst_listToVec _ isSemiformula_Padjoin (by rfl) _ hes (by row_entriesB), instOuter_subst_listToVec _ isSemiformula_Pnth (by rfl) _ hes (by row_entriesB), instOuter_subst_listToVec _ isSemiformula_Pnth (by rfl) _ hes (by row_entriesB)]
  all_goals try row_entries_simpB
  row_finish

/-! ## I. Numerals N4/N5 (§2.4), in the DSL -/

/-! ### `lengthZero` — `“x. …”`, `m = 1` -/

noncomputable def row_lengthZero_as : List V := []
noncomputable def row_lengthZero_c : V := subst LAct (listToVec [(𝟎 : V), (𝟎 : V)]) Plength

theorem quote_row_lengthZero : (⌜Semiformula.lMap emb lengthZeroB⌝ : V) = impChain LAct row_lengthZero_as row_lengthZero_c := by
  unfold lengthZeroB row_lengthZero_as row_lengthZero_c Plength
  all_goals row_shapeB

/-- `lengthZero` at the witnesses `[wx]` (the DSL variables right-to-left). -/
lemma inst_lengthZero {wx : V} (hwx : IsSemiterm LAct 0 wx) :
    row_lengthZero_as.map (instOuter LAct [wx]) = [] ∧
    instOuter LAct [wx] row_lengthZero_c = lengthFact (𝟎 : V) (𝟎 : V) := by
  have hes : ∀ e ∈ ([wx] : List V), IsSemiterm LAct 0 e := (List.forall_mem_cons.mpr ⟨hwx, List.forall_mem_nil _⟩)
  unfold row_lengthZero_as row_lengthZero_c
  simp only [List.map_cons, List.map_nil]
  rw [instOuter_subst_listToVec _ isSemiformula_Plength (by rfl) _ hes (by row_entriesB)]
  all_goals try row_entries_simpB
  row_finish

/-! ### `lengthOne` — `“x. …”`, `m = 1` -/

noncomputable def row_lengthOne_as : List V := []
noncomputable def row_lengthOne_c : V := subst LAct (listToVec [(𝟏 : V), (𝟏 : V)]) Plength

theorem quote_row_lengthOne : (⌜Semiformula.lMap emb lengthOneB⌝ : V) = impChain LAct row_lengthOne_as row_lengthOne_c := by
  unfold lengthOneB row_lengthOne_as row_lengthOne_c Plength
  all_goals row_shapeB

/-- `lengthOne` at the witnesses `[wx]` (the DSL variables right-to-left). -/
lemma inst_lengthOne {wx : V} (hwx : IsSemiterm LAct 0 wx) :
    row_lengthOne_as.map (instOuter LAct [wx]) = [] ∧
    instOuter LAct [wx] row_lengthOne_c = lengthFact (𝟏 : V) (𝟏 : V) := by
  have hes : ∀ e ∈ ([wx] : List V), IsSemiterm LAct 0 e := (List.forall_mem_cons.mpr ⟨hwx, List.forall_mem_nil _⟩)
  unfold row_lengthOne_as row_lengthOne_c
  simp only [List.map_cons, List.map_nil]
  rw [instOuter_subst_listToVec _ isSemiformula_Plength (by rfl) _ hes (by row_entriesB)]
  all_goals try row_entries_simpB
  row_finish

/-! ### `lengthTwoMul` — `“l x. …”`, `m = 2` -/

noncomputable def row_lengthTwoMul_as : List V := [subst LAct (listToVec [(𝟎 : V), bv 1]) Plt, subst LAct (listToVec [bv 0, bv 1]) Plength]
noncomputable def row_lengthTwoMul_c : V := subst LAct (listToVec [(bv 0 ^+ (𝟏 : V)), (((𝟏 : V) ^+ (𝟏 : V)) ^* bv 1)]) Plength

/-- `lengthTwoMul` at the witnesses `[wx, wl]` (the DSL variables right-to-left). -/
lemma inst_lengthTwoMul {wx wl : V} (hwx : IsSemiterm LAct 0 wx) (hwl : IsSemiterm LAct 0 wl) :
    row_lengthTwoMul_as.map (instOuter LAct [wx, wl]) = [ltFact (𝟎 : V) wx, lengthFact wl wx] ∧
    instOuter LAct [wx, wl] row_lengthTwoMul_c = lengthFact (wl ^+ (𝟏 : V)) (((𝟏 : V) ^+ (𝟏 : V)) ^* wx) := by
  have hes : ∀ e ∈ ([wx, wl] : List V), IsSemiterm LAct 0 e := (List.forall_mem_cons.mpr ⟨hwx, List.forall_mem_cons.mpr ⟨hwl, List.forall_mem_nil _⟩⟩)
  unfold row_lengthTwoMul_as row_lengthTwoMul_c
  simp only [List.map_cons, List.map_nil]
  rw [instOuter_subst_listToVec _ isSemiformula_Plt (by rfl) _ hes (by row_entriesB), instOuter_subst_listToVec _ isSemiformula_Plength (by rfl) _ hes (by row_entriesB), instOuter_subst_listToVec _ isSemiformula_Plength (by rfl) _ hes (by row_entriesB)]
  all_goals try row_entries_simpB
  row_finish

/-! ## J. `axm`(ii): `qqAlls`, `bv`, `termBV`, `listMax`, `fvarVec`, the `max`/`−` glue (§4.10(ii)) -/

/-! ### `qqAllsZero` — `“b. …”`, `m = 1` -/

noncomputable def row_qqAllsZero_as : List V := []
noncomputable def row_qqAllsZero_c : V := subst LAct (listToVec [bv 0, bv 0, (𝟎 : V)]) Palls

theorem quote_row_qqAllsZero : (⌜Semiformula.lMap emb qqAllsZeroB⌝ : V) = impChain LAct row_qqAllsZero_as row_qqAllsZero_c := by
  unfold qqAllsZeroB row_qqAllsZero_as row_qqAllsZero_c Palls
  all_goals row_shapeB

lemma isSemiformula_qqAllsZero_c : IsSemiformula LAct ((1 : ℕ) : V) row_qqAllsZero_c := by
  unfold row_qqAllsZero_c
  exact isSemiformula_substRow isSemiformula_Palls _ (by rfl) (by row_entriesB)

/-- `qqAllsZero` at the witnesses `[wb]` (the DSL variables right-to-left). -/
lemma inst_qqAllsZero {wb : V} (hwb : IsSemiterm LAct 0 wb) :
    row_qqAllsZero_as.map (instOuter LAct [wb]) = [] ∧
    instOuter LAct [wb] row_qqAllsZero_c = allsFact wb wb (𝟎 : V) := by
  have hes : ∀ e ∈ ([wb] : List V), IsSemiterm LAct 0 e := (List.forall_mem_cons.mpr ⟨hwb, List.forall_mem_nil _⟩)
  unfold row_qqAllsZero_as row_qqAllsZero_c
  simp only [List.map_cons, List.map_nil]
  rw [instOuter_subst_listToVec _ isSemiformula_Palls (by rfl) _ hes (by row_entriesB)]
  all_goals try row_entries_simpB
  row_finish

/-! ### `qqAllsSucc` — `“p' p b m. …”`, `m = 4` -/

noncomputable def row_qqAllsSucc_as : List V := [subst LAct (listToVec [bv 1, bv 2, bv 3]) Palls, subst LAct (listToVec [bv 0, bv 1]) Pall]
noncomputable def row_qqAllsSucc_c : V := subst LAct (listToVec [bv 0, bv 2, (bv 3 ^+ (𝟏 : V))]) Palls

theorem quote_row_qqAllsSucc : (⌜Semiformula.lMap emb qqAllsSuccB⌝ : V) = impChain LAct row_qqAllsSucc_as row_qqAllsSucc_c := by
  unfold qqAllsSuccB row_qqAllsSucc_as row_qqAllsSucc_c Pall Palls
  all_goals row_shapeB

lemma isSemiformula_qqAllsSucc_c : IsSemiformula LAct ((4 : ℕ) : V) row_qqAllsSucc_c := by
  unfold row_qqAllsSucc_c
  exact isSemiformula_substRow isSemiformula_Palls _ (by rfl) (by row_entriesB)

/-- `qqAllsSucc` at the witnesses `[wm, wb, wp, wpp]` (the DSL variables right-to-left). -/
lemma inst_qqAllsSucc {wm wb wp wpp : V} (hwm : IsSemiterm LAct 0 wm) (hwb : IsSemiterm LAct 0 wb) (hwp : IsSemiterm LAct 0 wp) (hwpp : IsSemiterm LAct 0 wpp) :
    row_qqAllsSucc_as.map (instOuter LAct [wm, wb, wp, wpp]) = [allsFact wp wb wm, allFact wpp wp] ∧
    instOuter LAct [wm, wb, wp, wpp] row_qqAllsSucc_c = allsFact wpp wb (wm ^+ (𝟏 : V)) := by
  have hes : ∀ e ∈ ([wm, wb, wp, wpp] : List V), IsSemiterm LAct 0 e := (List.forall_mem_cons.mpr ⟨hwm, List.forall_mem_cons.mpr ⟨hwb, List.forall_mem_cons.mpr ⟨hwp, List.forall_mem_cons.mpr ⟨hwpp, List.forall_mem_nil _⟩⟩⟩⟩)
  unfold row_qqAllsSucc_as row_qqAllsSucc_c
  simp only [List.map_cons, List.map_nil]
  rw [instOuter_subst_listToVec _ isSemiformula_Palls (by rfl) _ hes (by row_entriesB), instOuter_subst_listToVec _ isSemiformula_Pall (by rfl) _ hes (by row_entriesB), instOuter_subst_listToVec _ isSemiformula_Palls (by rfl) _ hes (by row_entriesB)]
  all_goals try row_entries_simpB
  row_finish

/-! ### `fvarVecNth` — `“e fv m i. …”`, `m = 4` -/

noncomputable def row_fvarVecNth_as : List V := [subst LAct (listToVec [bv 3, bv 2]) Plt, subst LAct (listToVec [bv 1, bv 2]) PfvarVec, subst LAct (listToVec [bv 0, bv 3]) Pfvar]
noncomputable def row_fvarVecNth_c : V := subst LAct (listToVec [bv 0, bv 1, bv 3]) Pnth

/-- `fvarVecNth` at the witnesses `[wi, wm, wfv, we]` (the DSL variables right-to-left). -/
lemma inst_fvarVecNth {wi wm wfv we : V} (hwi : IsSemiterm LAct 0 wi) (hwm : IsSemiterm LAct 0 wm) (hwfv : IsSemiterm LAct 0 wfv) (hwe : IsSemiterm LAct 0 we) :
    row_fvarVecNth_as.map (instOuter LAct [wi, wm, wfv, we]) = [ltFact wi wm, fvarVecFact wfv wm, fvarFact we wi] ∧
    instOuter LAct [wi, wm, wfv, we] row_fvarVecNth_c = nthFact we wfv wi := by
  have hes : ∀ e ∈ ([wi, wm, wfv, we] : List V), IsSemiterm LAct 0 e := (List.forall_mem_cons.mpr ⟨hwi, List.forall_mem_cons.mpr ⟨hwm, List.forall_mem_cons.mpr ⟨hwfv, List.forall_mem_cons.mpr ⟨hwe, List.forall_mem_nil _⟩⟩⟩⟩)
  unfold row_fvarVecNth_as row_fvarVecNth_c
  simp only [List.map_cons, List.map_nil]
  rw [instOuter_subst_listToVec _ isSemiformula_Plt (by rfl) _ hes (by row_entriesB), instOuter_subst_listToVec _ isSemiformula_PfvarVec (by rfl) _ hes (by row_entriesB), instOuter_subst_listToVec _ isSemiformula_Pfvar (by rfl) _ hes (by row_entriesB), instOuter_subst_listToVec _ isSemiformula_Pnth (by rfl) _ hes (by row_entriesB)]
  all_goals try row_entries_simpB
  row_finish

/-! ## K. Chains: the `Sets`/`Lengths` rows of §3.4 re-issued with `inst_` lemmas (`Layout.chainSteps`) -/

/-! ### `insertTotalC` — `“s x. …”`, `m = 2` -/

noncomputable def row_insertTotalC_as : List V := []
noncomputable def row_insertTotalC_body : V := subst LAct (listToVec [bv 0, bv 2, bv 1]) Pinsert
noncomputable def row_insertTotalC_R : V := row_insertTotalC_body
noncomputable def row_insertTotalC_c : V := ^∃ row_insertTotalC_R

theorem quote_row_insertTotalC : (⌜Semiformula.lMap emb insertTotalCB⌝ : V) = impChain LAct row_insertTotalC_as row_insertTotalC_c := by
  unfold insertTotalCB row_insertTotalC_as row_insertTotalC_c row_insertTotalC_R row_insertTotalC_body Pinsert
  all_goals row_shapeB

lemma isSemiformula_insertTotalC_R : IsSemiformula LAct ((3 : ℕ) : V) row_insertTotalC_R := by
  unfold row_insertTotalC_R row_insertTotalC_body
  exact isSemiformula_substRow isSemiformula_Pinsert _ (by rfl) (by row_entriesB)
lemma row_insertTotalC_R_eq : (row_insertTotalC_R : V) = exsIter 0 row_insertTotalC_body := rfl

/-- `insertTotalC` at the witnesses `[wx, ws]` (the DSL variables right-to-left). -/
lemma inst_insertTotalC {wx ws : V} (hwx : IsSemiterm LAct 0 wx) (hws : IsSemiterm LAct 0 ws) :
    row_insertTotalC_as.map (instOuter LAct [wx, ws]) = [] ∧
    freeIter LAct 1 (instOuterAt LAct 1 [wx, ws] row_insertTotalC_body) = insFact (^&((0 : ℕ) : V)) (termShift LAct wx) (termShift LAct ws) := by
  have hes : ∀ e ∈ ([wx, ws] : List V), IsSemiterm LAct 0 e := (List.forall_mem_cons.mpr ⟨hwx, List.forall_mem_cons.mpr ⟨hws, List.forall_mem_nil _⟩⟩)
  unfold row_insertTotalC_as row_insertTotalC_body
  simp only [List.map_cons, List.map_nil]
  refine ⟨by ((try row_entries_simpB); row_finish), ?_⟩
  · rw [instOuterAt_subst_listToVec 1 _ isSemiformula_Pinsert (by rfl) _ hes (by row_entriesB)]
    row_entries_simpB
    rw [freeIter_subst_listToVec' 1 _ isSemiformula_Pinsert shift_Pinsert (by rfl) (by row_entriesB)]
    simp only [List.map_cons, List.map_nil]
    rw [freeIterT_bv0 1 0 (by norm_num), freeIterT_closed 0 hws 1, freeIterT_closed 0 hwx 1]
    try rfl

/-! ### `memInsertSelfC` — `“t s x. …”`, `m = 3` -/

noncomputable def row_memInsertSelfC_as : List V := [subst LAct (listToVec [bv 0, bv 2, bv 1]) Pinsert]
noncomputable def row_memInsertSelfC_c : V := subst LAct (listToVec [bv 2, bv 0]) Pmem

theorem quote_row_memInsertSelfC : (⌜Semiformula.lMap emb memInsertSelfCB⌝ : V) = impChain LAct row_memInsertSelfC_as row_memInsertSelfC_c := by
  unfold memInsertSelfCB row_memInsertSelfC_as row_memInsertSelfC_c Pinsert Pmem
  all_goals row_shapeB

lemma isSemiformula_memInsertSelfC_c : IsSemiformula LAct ((3 : ℕ) : V) row_memInsertSelfC_c := by
  unfold row_memInsertSelfC_c
  exact isSemiformula_substRow isSemiformula_Pmem _ (by rfl) (by row_entriesB)

/-- `memInsertSelfC` at the witnesses `[wx, ws, wt]` (the DSL variables right-to-left). -/
lemma inst_memInsertSelfC {wx ws wt : V} (hwx : IsSemiterm LAct 0 wx) (hws : IsSemiterm LAct 0 ws) (hwt : IsSemiterm LAct 0 wt) :
    row_memInsertSelfC_as.map (instOuter LAct [wx, ws, wt]) = [insFact wt wx ws] ∧
    instOuter LAct [wx, ws, wt] row_memInsertSelfC_c = memFact wx wt := by
  have hes : ∀ e ∈ ([wx, ws, wt] : List V), IsSemiterm LAct 0 e := (List.forall_mem_cons.mpr ⟨hwx, List.forall_mem_cons.mpr ⟨hws, List.forall_mem_cons.mpr ⟨hwt, List.forall_mem_nil _⟩⟩⟩)
  unfold row_memInsertSelfC_as row_memInsertSelfC_c
  simp only [List.map_cons, List.map_nil]
  rw [instOuter_subst_listToVec _ isSemiformula_Pinsert (by rfl) _ hes (by row_entriesB), instOuter_subst_listToVec _ isSemiformula_Pmem (by rfl) _ hes (by row_entriesB)]
  all_goals try row_entries_simpB
  row_finish

/-! ### `subsetInsertC` — `“t s x. …”`, `m = 3` -/

noncomputable def row_subsetInsertC_as : List V := [subst LAct (listToVec [bv 0, bv 2, bv 1]) Pinsert]
noncomputable def row_subsetInsertC_c : V := subst LAct (listToVec [bv 1, bv 0]) Psubset

theorem quote_row_subsetInsertC : (⌜Semiformula.lMap emb subsetInsertCB⌝ : V) = impChain LAct row_subsetInsertC_as row_subsetInsertC_c := by
  unfold subsetInsertCB row_subsetInsertC_as row_subsetInsertC_c Pinsert Psubset
  all_goals row_shapeB

lemma isSemiformula_subsetInsertC_c : IsSemiformula LAct ((3 : ℕ) : V) row_subsetInsertC_c := by
  unfold row_subsetInsertC_c
  exact isSemiformula_substRow isSemiformula_Psubset _ (by rfl) (by row_entriesB)

/-- `subsetInsertC` at the witnesses `[wx, ws, wt]` (the DSL variables right-to-left). -/
lemma inst_subsetInsertC {wx ws wt : V} (hwx : IsSemiterm LAct 0 wx) (hws : IsSemiterm LAct 0 ws) (hwt : IsSemiterm LAct 0 wt) :
    row_subsetInsertC_as.map (instOuter LAct [wx, ws, wt]) = [insFact wt wx ws] ∧
    instOuter LAct [wx, ws, wt] row_subsetInsertC_c = subsetFact ws wt := by
  have hes : ∀ e ∈ ([wx, ws, wt] : List V), IsSemiterm LAct 0 e := (List.forall_mem_cons.mpr ⟨hwx, List.forall_mem_cons.mpr ⟨hws, List.forall_mem_cons.mpr ⟨hwt, List.forall_mem_nil _⟩⟩⟩)
  unfold row_subsetInsertC_as row_subsetInsertC_c
  simp only [List.map_cons, List.map_nil]
  rw [instOuter_subst_listToVec _ isSemiformula_Pinsert (by rfl) _ hes (by row_entriesB), instOuter_subst_listToVec _ isSemiformula_Psubset (by rfl) _ hes (by row_entriesB)]
  all_goals try row_entries_simpB
  row_finish

/-! ### `subsetTransC` — `“u t s. …”`, `m = 3` -/

noncomputable def row_subsetTransC_as : List V := [subst LAct (listToVec [bv 2, bv 1]) Psubset, subst LAct (listToVec [bv 1, bv 0]) Psubset]
noncomputable def row_subsetTransC_c : V := subst LAct (listToVec [bv 2, bv 0]) Psubset

theorem quote_row_subsetTransC : (⌜Semiformula.lMap emb subsetTransCB⌝ : V) = impChain LAct row_subsetTransC_as row_subsetTransC_c := by
  unfold subsetTransCB row_subsetTransC_as row_subsetTransC_c Psubset
  all_goals row_shapeB

lemma isSemiformula_subsetTransC_c : IsSemiformula LAct ((3 : ℕ) : V) row_subsetTransC_c := by
  unfold row_subsetTransC_c
  exact isSemiformula_substRow isSemiformula_Psubset _ (by rfl) (by row_entriesB)

/-- `subsetTransC` at the witnesses `[ws, wt, wu]` (the DSL variables right-to-left). -/
lemma inst_subsetTransC {ws wt wu : V} (hws : IsSemiterm LAct 0 ws) (hwt : IsSemiterm LAct 0 wt) (hwu : IsSemiterm LAct 0 wu) :
    row_subsetTransC_as.map (instOuter LAct [ws, wt, wu]) = [subsetFact ws wt, subsetFact wt wu] ∧
    instOuter LAct [ws, wt, wu] row_subsetTransC_c = subsetFact ws wu := by
  have hes : ∀ e ∈ ([ws, wt, wu] : List V), IsSemiterm LAct 0 e := (List.forall_mem_cons.mpr ⟨hws, List.forall_mem_cons.mpr ⟨hwt, List.forall_mem_cons.mpr ⟨hwu, List.forall_mem_nil _⟩⟩⟩)
  unfold row_subsetTransC_as row_subsetTransC_c
  simp only [List.map_cons, List.map_nil]
  rw [instOuter_subst_listToVec _ isSemiformula_Psubset (by rfl) _ hes (by row_entriesB), instOuter_subst_listToVec _ isSemiformula_Psubset (by rfl) _ hes (by row_entriesB), instOuter_subst_listToVec _ isSemiformula_Psubset (by rfl) _ hes (by row_entriesB)]
  all_goals try row_entries_simpB
  row_finish

/-! ### `subsetMemC` — `“x t s. …”`, `m = 3` -/

noncomputable def row_subsetMemC_as : List V := [subst LAct (listToVec [bv 2, bv 1]) Psubset, subst LAct (listToVec [bv 0, bv 2]) Pmem]
noncomputable def row_subsetMemC_c : V := subst LAct (listToVec [bv 0, bv 1]) Pmem

theorem quote_row_subsetMemC : (⌜Semiformula.lMap emb subsetMemCB⌝ : V) = impChain LAct row_subsetMemC_as row_subsetMemC_c := by
  unfold subsetMemCB row_subsetMemC_as row_subsetMemC_c Pmem Psubset
  all_goals row_shapeB

lemma isSemiformula_subsetMemC_c : IsSemiformula LAct ((3 : ℕ) : V) row_subsetMemC_c := by
  unfold row_subsetMemC_c
  exact isSemiformula_substRow isSemiformula_Pmem _ (by rfl) (by row_entriesB)

/-- `subsetMemC` at the witnesses `[ws, wt, wx]` (the DSL variables right-to-left). -/
lemma inst_subsetMemC {ws wt wx : V} (hws : IsSemiterm LAct 0 ws) (hwt : IsSemiterm LAct 0 wt) (hwx : IsSemiterm LAct 0 wx) :
    row_subsetMemC_as.map (instOuter LAct [ws, wt, wx]) = [subsetFact ws wt, memFact wx ws] ∧
    instOuter LAct [ws, wt, wx] row_subsetMemC_c = memFact wx wt := by
  have hes : ∀ e ∈ ([ws, wt, wx] : List V), IsSemiterm LAct 0 e := (List.forall_mem_cons.mpr ⟨hws, List.forall_mem_cons.mpr ⟨hwt, List.forall_mem_cons.mpr ⟨hwx, List.forall_mem_nil _⟩⟩⟩)
  unfold row_subsetMemC_as row_subsetMemC_c
  simp only [List.map_cons, List.map_nil]
  rw [instOuter_subst_listToVec _ isSemiformula_Psubset (by rfl) _ hes (by row_entriesB), instOuter_subst_listToVec _ isSemiformula_Pmem (by rfl) _ hes (by row_entriesB), instOuter_subst_listToVec _ isSemiformula_Pmem (by rfl) _ hes (by row_entriesB)]
  all_goals try row_entries_simpB
  row_finish

/-! ### `emptySubsetC` — `“s. …”`, `m = 1` -/

noncomputable def row_emptySubsetC_as : List V := []
noncomputable def row_emptySubsetC_c : V := subst LAct (listToVec [(𝟎 : V), bv 0]) Psubset

theorem quote_row_emptySubsetC : (⌜Semiformula.lMap emb emptySubsetCB⌝ : V) = impChain LAct row_emptySubsetC_as row_emptySubsetC_c := by
  unfold emptySubsetCB row_emptySubsetC_as row_emptySubsetC_c Psubset
  all_goals row_shapeB

lemma isSemiformula_emptySubsetC_c : IsSemiformula LAct ((1 : ℕ) : V) row_emptySubsetC_c := by
  unfold row_emptySubsetC_c
  exact isSemiformula_substRow isSemiformula_Psubset _ (by rfl) (by row_entriesB)

/-- `emptySubsetC` at the witnesses `[ws]` (the DSL variables right-to-left). -/
lemma inst_emptySubsetC {ws : V} (hws : IsSemiterm LAct 0 ws) :
    row_emptySubsetC_as.map (instOuter LAct [ws]) = [] ∧
    instOuter LAct [ws] row_emptySubsetC_c = subsetFact (𝟎 : V) ws := by
  have hes : ∀ e ∈ ([ws] : List V), IsSemiterm LAct 0 e := (List.forall_mem_cons.mpr ⟨hws, List.forall_mem_nil _⟩)
  unfold row_emptySubsetC_as row_emptySubsetC_c
  simp only [List.map_cons, List.map_nil]
  rw [instOuter_subst_listToVec _ isSemiformula_Psubset (by rfl) _ hes (by row_entriesB)]
  all_goals try row_entries_simpB
  row_finish

/-! ### `fsetOfSubsetZeroC` — `“s. …”`, `m = 1` -/

noncomputable def row_fsetOfSubsetZeroC_as : List V := [subst LAct (listToVec [bv 0, (𝟎 : V)]) Psubset]
noncomputable def row_fsetOfSubsetZeroC_c : V := subst LAct (listToVec [bv 0]) PfsetSigma

theorem quote_row_fsetOfSubsetZeroC : (⌜Semiformula.lMap emb fsetOfSubsetZeroCB⌝ : V) = impChain LAct row_fsetOfSubsetZeroC_as row_fsetOfSubsetZeroC_c := by
  unfold fsetOfSubsetZeroCB row_fsetOfSubsetZeroC_as row_fsetOfSubsetZeroC_c PfsetSigma Psubset
  all_goals row_shapeB

lemma isSemiformula_fsetOfSubsetZeroC_c : IsSemiformula LAct ((1 : ℕ) : V) row_fsetOfSubsetZeroC_c := by
  unfold row_fsetOfSubsetZeroC_c
  exact isSemiformula_substRow isSemiformula_PfsetSigma _ (by rfl) (by row_entriesB)

/-- `fsetOfSubsetZeroC` at the witnesses `[ws]` (the DSL variables right-to-left). -/
lemma inst_fsetOfSubsetZeroC {ws : V} (hws : IsSemiterm LAct 0 ws) :
    row_fsetOfSubsetZeroC_as.map (instOuter LAct [ws]) = [subsetFact ws (𝟎 : V)] ∧
    instOuter LAct [ws] row_fsetOfSubsetZeroC_c = fsetSigmaFact ws := by
  have hes : ∀ e ∈ ([ws] : List V), IsSemiterm LAct 0 e := (List.forall_mem_cons.mpr ⟨hws, List.forall_mem_nil _⟩)
  unfold row_fsetOfSubsetZeroC_as row_fsetOfSubsetZeroC_c
  simp only [List.map_cons, List.map_nil]
  rw [instOuter_subst_listToVec _ isSemiformula_Psubset (by rfl) _ hes (by row_entriesB), instOuter_subst_listToVec _ isSemiformula_PfsetSigma (by rfl) _ hes (by row_entriesB)]
  all_goals try row_entries_simpB
  row_finish

/-! ### `isFormulaSetInsertC` — `“t p s. …”`, `m = 3` -/

noncomputable def row_isFormulaSetInsertC_as : List V := [subst LAct (listToVec [bv 2]) PfsetPi, subst LAct (listToVec [(𝟎 : V), bv 1]) Ppi, subst LAct (listToVec [bv 0, bv 1, bv 2]) Pinsert]
noncomputable def row_isFormulaSetInsertC_c : V := subst LAct (listToVec [bv 0]) PfsetSigma

theorem quote_row_isFormulaSetInsertC : (⌜Semiformula.lMap emb isFormulaSetInsertCB⌝ : V) = impChain LAct row_isFormulaSetInsertC_as row_isFormulaSetInsertC_c := by
  unfold isFormulaSetInsertCB row_isFormulaSetInsertC_as row_isFormulaSetInsertC_c PfsetPi PfsetSigma Pinsert Ppi
  all_goals row_shapeB

lemma isSemiformula_isFormulaSetInsertC_c : IsSemiformula LAct ((3 : ℕ) : V) row_isFormulaSetInsertC_c := by
  unfold row_isFormulaSetInsertC_c
  exact isSemiformula_substRow isSemiformula_PfsetSigma _ (by rfl) (by row_entriesB)

/-- `isFormulaSetInsertC` at the witnesses `[ws, wp, wt]` (the DSL variables right-to-left). -/
lemma inst_isFormulaSetInsertC {ws wp wt : V} (hws : IsSemiterm LAct 0 ws) (hwp : IsSemiterm LAct 0 wp) (hwt : IsSemiterm LAct 0 wt) :
    row_isFormulaSetInsertC_as.map (instOuter LAct [ws, wp, wt]) = [fsetPiFact ws, piFact (𝟎 : V) wp, insFact wt wp ws] ∧
    instOuter LAct [ws, wp, wt] row_isFormulaSetInsertC_c = fsetSigmaFact wt := by
  have hes : ∀ e ∈ ([ws, wp, wt] : List V), IsSemiterm LAct 0 e := (List.forall_mem_cons.mpr ⟨hws, List.forall_mem_cons.mpr ⟨hwp, List.forall_mem_cons.mpr ⟨hwt, List.forall_mem_nil _⟩⟩⟩)
  unfold row_isFormulaSetInsertC_as row_isFormulaSetInsertC_c
  simp only [List.map_cons, List.map_nil]
  rw [instOuter_subst_listToVec _ isSemiformula_PfsetPi (by rfl) _ hes (by row_entriesB), instOuter_subst_listToVec _ isSemiformula_Ppi (by rfl) _ hes (by row_entriesB), instOuter_subst_listToVec _ isSemiformula_Pinsert (by rfl) _ hes (by row_entriesB), instOuter_subst_listToVec _ isSemiformula_PfsetSigma (by rfl) _ hes (by row_entriesB)]
  all_goals try row_entries_simpB
  row_finish

/-! ### `fsetSigmaPiC` — `“s. …”`, `m = 1` -/

noncomputable def row_fsetSigmaPiC_as : List V := [subst LAct (listToVec [bv 0]) PfsetSigma]
noncomputable def row_fsetSigmaPiC_c : V := subst LAct (listToVec [bv 0]) PfsetPi

theorem quote_row_fsetSigmaPiC : (⌜Semiformula.lMap emb fsetSigmaPiCB⌝ : V) = impChain LAct row_fsetSigmaPiC_as row_fsetSigmaPiC_c := by
  unfold fsetSigmaPiCB row_fsetSigmaPiC_as row_fsetSigmaPiC_c PfsetPi PfsetSigma
  all_goals row_shapeB

lemma isSemiformula_fsetSigmaPiC_c : IsSemiformula LAct ((1 : ℕ) : V) row_fsetSigmaPiC_c := by
  unfold row_fsetSigmaPiC_c
  exact isSemiformula_substRow isSemiformula_PfsetPi _ (by rfl) (by row_entriesB)

/-- `fsetSigmaPiC` at the witnesses `[ws]` (the DSL variables right-to-left). -/
lemma inst_fsetSigmaPiC {ws : V} (hws : IsSemiterm LAct 0 ws) :
    row_fsetSigmaPiC_as.map (instOuter LAct [ws]) = [fsetSigmaFact ws] ∧
    instOuter LAct [ws] row_fsetSigmaPiC_c = fsetPiFact ws := by
  have hes : ∀ e ∈ ([ws] : List V), IsSemiterm LAct 0 e := (List.forall_mem_cons.mpr ⟨hws, List.forall_mem_nil _⟩)
  unfold row_fsetSigmaPiC_as row_fsetSigmaPiC_c
  simp only [List.map_cons, List.map_nil]
  rw [instOuter_subst_listToVec _ isSemiformula_PfsetSigma (by rfl) _ hes (by row_entriesB), instOuter_subst_listToVec _ isSemiformula_PfsetPi (by rfl) _ hes (by row_entriesB)]
  all_goals try row_entries_simpB
  row_finish

/-! ### `sequentLenTotalC` — `“s. …”`, `m = 1` -/

noncomputable def row_sequentLenTotalC_as : List V := []
noncomputable def row_sequentLenTotalC_body : V := subst LAct (listToVec [bv 0, bv 1]) PsetLen
noncomputable def row_sequentLenTotalC_R : V := row_sequentLenTotalC_body
noncomputable def row_sequentLenTotalC_c : V := ^∃ row_sequentLenTotalC_R

theorem quote_row_sequentLenTotalC : (⌜Semiformula.lMap emb sequentLenTotalCB⌝ : V) = impChain LAct row_sequentLenTotalC_as row_sequentLenTotalC_c := by
  unfold sequentLenTotalCB row_sequentLenTotalC_as row_sequentLenTotalC_c row_sequentLenTotalC_R row_sequentLenTotalC_body PsetLen
  all_goals row_shapeB

lemma isSemiformula_sequentLenTotalC_R : IsSemiformula LAct ((2 : ℕ) : V) row_sequentLenTotalC_R := by
  unfold row_sequentLenTotalC_R row_sequentLenTotalC_body
  exact isSemiformula_substRow isSemiformula_PsetLen _ (by rfl) (by row_entriesB)
lemma row_sequentLenTotalC_R_eq : (row_sequentLenTotalC_R : V) = exsIter 0 row_sequentLenTotalC_body := rfl

/-- `sequentLenTotalC` at the witnesses `[ws]` (the DSL variables right-to-left). -/
lemma inst_sequentLenTotalC {ws : V} (hws : IsSemiterm LAct 0 ws) :
    row_sequentLenTotalC_as.map (instOuter LAct [ws]) = [] ∧
    freeIter LAct 1 (instOuterAt LAct 1 [ws] row_sequentLenTotalC_body) = sequentLenFact (^&((0 : ℕ) : V)) (termShift LAct ws) := by
  have hes : ∀ e ∈ ([ws] : List V), IsSemiterm LAct 0 e := (List.forall_mem_cons.mpr ⟨hws, List.forall_mem_nil _⟩)
  unfold row_sequentLenTotalC_as row_sequentLenTotalC_body
  simp only [List.map_cons, List.map_nil]
  refine ⟨by ((try row_entries_simpB); row_finish), ?_⟩
  · rw [instOuterAt_subst_listToVec 1 _ isSemiformula_PsetLen (by rfl) _ hes (by row_entriesB)]
    row_entries_simpB
    rw [freeIter_subst_listToVec' 1 _ isSemiformula_PsetLen shift_PsetLen (by rfl) (by row_entriesB)]
    simp only [List.map_cons, List.map_nil]
    rw [freeIterT_bv0 1 0 (by norm_num), freeIterT_closed 0 hws 1]
    try rfl

/-! ### `subsetReflC` — `“s. …”`, `m = 1` -/

noncomputable def row_subsetReflC_as : List V := []
noncomputable def row_subsetReflC_c : V := subst LAct (listToVec [bv 0, bv 0]) Psubset

theorem quote_row_subsetReflC : (⌜Semiformula.lMap emb subsetReflCB⌝ : V) = impChain LAct row_subsetReflC_as row_subsetReflC_c := by
  unfold subsetReflCB row_subsetReflC_as row_subsetReflC_c Psubset
  all_goals row_shapeB

lemma isSemiformula_subsetReflC_c : IsSemiformula LAct ((1 : ℕ) : V) row_subsetReflC_c := by
  unfold row_subsetReflC_c
  exact isSemiformula_substRow isSemiformula_Psubset _ (by rfl) (by row_entriesB)

/-- `subsetReflC` at the witnesses `[ws]` (the DSL variables right-to-left). -/
lemma inst_subsetReflC {ws : V} (hws : IsSemiterm LAct 0 ws) :
    row_subsetReflC_as.map (instOuter LAct [ws]) = [] ∧
    instOuter LAct [ws] row_subsetReflC_c = subsetFact ws ws := by
  have hes : ∀ e ∈ ([ws] : List V), IsSemiterm LAct 0 e := (List.forall_mem_cons.mpr ⟨hws, List.forall_mem_nil _⟩)
  unfold row_subsetReflC_as row_subsetReflC_c
  simp only [List.map_cons, List.map_nil]
  rw [instOuter_subst_listToVec _ isSemiformula_Psubset (by rfl) _ hes (by row_entriesB)]
  all_goals try row_entries_simpB
  row_finish

end rows

end ArithS
