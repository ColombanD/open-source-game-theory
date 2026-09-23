import ArithS.Necessitation.Package

/-!
# ArithS.Necessitation.ClosedNec — U10 in CLOSED-SENTENCE, ARBITRARY-BUDGET form

`Package.boundedInnerNec_sixteen` is PARAMETRIC: it takes a proof of the `k`-instance `instB ⌜χ⌝ k` of a
one-variable formula `χ` at the budget `gBudget k = ‖k‖³` and returns a proof of the `k`-instance of the
box `Box_g χ`. Route B (`ROUTE_B_SCOPE.md` §3 Phase 0) needs the same construction for a CLOSED sentence
`σ` at an ARBITRARY budget `b` — the moment one bot cites another searcher's success at the partner's
full budget. This file delivers it:

    closedInnerNec_sixteen : ∀ σ : Sentence LAct, ∃ C : ℕ, ∀ V b,
      LenDerivable TAct b ⌜σ⌝ → ∃ e ≤ C·(b^16 + 1), LenDerivable TAct e (boxSentenceCode σ b)

where `boxSentenceCode σ b := instB ⌜boxClosed σ⌝ b` is the CODE of the `LAct`-sentence
"`σ` has a `TAct`-proof of length `≤ b`" with `b` written as the BINARY NUMERAL TERM `bnum b` and `σ`
named by its (unary) Gödel numeral — `boxClosed σ := lenDerivableDef ⇜ ![#0, ⌜σ⌝]`, the budget in the
free slot `#0`, exactly as `Prep.Box_g` fills its slots; the code equation is
`boxSentenceCode_eq : boxSentenceCode σ b = lenDerFact (bnum b) (numeral ⌜σ⌝)` and the semantics is
`eval_boxSentence_iff` (in every `LAct`-structure with a standard `ℒₒᵣ`-reduct; `_std`/`_swap` are the two
standard readings).

## Where the parametric kit hard-codes `gBudget k`/`instB`, and what is replaced

The verification kit itself (`Assemble.VerifyKit'''`: `rootSteps_ok`, `vList`, the cost half) is stated for
an ARBITRARY conclusion `x` and cap `E` — it is re-used verbatim. Three pieces of `Top.lean`/`Assemble.lean`
are specific to the parametric form and are replaced here, none of them modified:

* the PIN (`PinKit'`: `instBFact &(i+2) (qNum χ) (bnum k)` via the certified substitution) — replaced by the
  numeral identification `NumId.numId_sentence σ` on the ROOT DOSSIER (`RootLayout.1`), which leaves
  `eqFact &(i+2) (numeral ⌜σ⌝)` with a shift-free list of standard length `Cσ`;
* the CLOSING BLOCK (`closeSteps`: the three numeral lemmas N5/N4/N4 computing `‖k‖³`, `gIntroNum`,
  `boxIntro` into `boxFact`) — replaced by `closeStepsC`: `goalElim`, the ONE numeral lemma
  `leFact (bnum (dlen ρ)) (bnum b)` (`NumSteps.leCode`), `dlenDefIntro`, `proofIntro`, `leTrans`,
  `lenDerIntro` at `wa := bnum b`, and ONE NEW ROW, the equality congruence
  `lenDerCong : ∀ g' g a, LenDer a g → g = g' → LenDer a g'` (§2 — `Lib` by truth in every model), which
  replaces the eigenvariable `&(js+3)` by the numeral of `σ`;
* the COST ARITHMETIC (`boundedInnerNec_of_kit'''`, graded in `G = gBudget k + 1`, `u = ‖k‖ + 1`) —
  redone at `G = b + 1`, `u = 1` (every `u`-graded quantity of the parametric top — the pin length
  `Cχ(‖k‖+1)`, the walk length `12|instB ⌜χ⌝ k|+9` — is a CONSTANT of `σ` here), through the SAME
  `Top.topBound''_pb`, so the degree is again `deg 4 = 16`.

The new row lives in an EXTENDED table (`closedRows := indRecRows ++ [lenDerCongRow]`, §3): every table
predicate of the chain is a PREFIX predicate, so the extended table is an `IndRec` table, and the package is
re-derived exactly as `Package.kitPackage'''_of_size'` (§7) on it. No existing file changes.

## Contents

* §1 the closed box: `boxClosed`, `eval_boxSentence_iff` (+ `_std`, `_swap`), `qNumS`, `boxSentenceCode`,
  `quote_boxClosed`, `boxSentenceCode_eq`, `boxSentenceCode_nat` (the ℕ reading: the quote of the instance).
* §2 the congruence row `lenDerCong` and its `RowInstB` pieces; `stepLenDerCong`/`tok_lenDerCong`.
* §3 the extended table `ClosedTable`, `exists_closedTableB`.
* §4 the closing block `closeStepsC`/`closeStepsC_ok`.
* §5 the top `top_mainC` (the four blocks, the derivation, the explicit `topBound''` bound at `lk = 0`).
* §6 the package `KitPackageC` and `kitPackageC_of`, `closedInnerNec_of_kit`.
* §7 the headline `closedInnerNec_sixteen` (+ `closedInnerNec_sixteen'`, the numeral-free reading).
-/

namespace ArithS

open FFL FFL.FirstOrder Arithmetic Bootstrapping
open FFL.FirstOrder.Arithmetic.Bootstrapping.Arithmetic
open PeanoMinus ISigma0 ISigma1
open LAct

set_option linter.unusedSimpArgs false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false
set_option linter.unusedSectionVars false
set_option maxRecDepth 20000

variable {V : Type} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

/-! ## 1. The closed box -/

section closedBox

/-- `LenDerivable TAct a g` as an `LAct`-semisentence (`a g` = budget, formula). -/
noncomputable def lenDerA : Semisentence LAct 2 :=
  Semiformula.lMap emb (↑(lenDerivableDef TAct) : ArithmeticSemisentence 2)

/-- **The closed box**: `boxClosed σ (b) := LenDerivable b ⌜σ⌝`, the budget in the free slot `#0` and the
sentence named by its Gödel numeral (an astronomical CONSTANT, never evaluated — the `Box_g` discipline). -/
noncomputable def boxClosed (σ : Sentence LAct) : Semisentence LAct 1 :=
  lenDerA ⇜ ![#0, Semiterm.lMap emb (⌜σ⌝ : ArithmeticSemiterm Empty 1)]

lemma boxClosed_def (σ : Sentence LAct) :
    boxClosed σ = lenDerA ⇜ ![#0, Semiterm.lMap emb (⌜σ⌝ : ArithmeticSemiterm Empty 1)] := rfl

/-- **The semantics of the closed box** in every `LAct`-structure on `V` whose `ℒₒᵣ`-reduct is standard:
`boxClosed σ (b)` holds iff `⌜σ⌝` has a `TAct`-proof code of length `≤ b`. -/
theorem eval_boxSentence_iff (σ : Sentence LAct) (S : Structure LAct V)
    (hS : Structure.lMap emb S = standardModel V) (b : V) :
    Semiformula.Eval (s := S) ![b] Empty.elim (boxClosed σ) ↔ LenDerivable TAct b (⌜σ⌝ : V) := by
  rw [boxClosed_def, Semiformula.eval_substs]
  have hv : (Semiterm.val (s := S) (b :> ![]) Empty.elim ∘
      ![#0, Semiterm.lMap emb (⌜σ⌝ : ArithmeticSemiterm Empty 1)]) = ![b, (⌜σ⌝ : V)] := by
    funext i; fin_cases i
    · rfl
    · exact val_lMap_gödel S hS σ _
  rw [hv]
  unfold lenDerA
  rw [Semiformula.eval_lMap, hS]
  simp [(LenDerivable.defined (V := V) TAct).iff]

theorem eval_boxSentence_iff_std (σ : Sentence LAct) (b : V) :
    Semiformula.Eval (s := stdActS V) ![b] Empty.elim (boxClosed σ) ↔ LenDerivable TAct b (⌜σ⌝ : V) :=
  eval_boxSentence_iff σ _ stdActS_lMap_emb b

theorem eval_boxSentence_iff_swap (σ : Sentence LAct) (b : V) :
    Semiformula.Eval (s := swapActS V) ![b] Empty.elim (boxClosed σ) ↔ LenDerivable TAct b (⌜σ⌝ : V) :=
  eval_boxSentence_iff σ _ swapActS_lMap_emb b

/-- The unary numeral term of `⌜σ⌝` (the closed-sentence twin of `Top.qNum`). -/
noncomputable def qNumS (σ : Sentence LAct) : V := numeral (⌜σ⌝ : V)

lemma isSemiterm_qNumS (σ : Sentence LAct) : IsSemiterm LAct (0 : V) (qNumS σ) :=
  InstV.isSemiterm_LAct_of_LOR (numeral_semiterm 0 _)

lemma termShiftIterV_qNumS (σ : Sentence LAct) : ∀ c : V, termShiftIterV (qNumS σ : V) c = qNumS σ :=
  termShiftIterV_numeral _

/-- The numeral's length is a STANDARD constant of `σ`. -/
lemma termLen_qNumS_le (σ : Sentence LAct) :
    termLen LAct (qNumS σ : V) ≤ ((2 * (⌜σ⌝ : ℕ) + 1 : ℕ) : V) := by
  unfold qNumS
  push_cast
  rw [Sentence.coe_quote_eq_quote σ]
  exact termLen_numeral_le _

/-- **The closed box CODE at the budget `b`**: the `b`-instance (binary numeral) of `⌜boxClosed σ⌝`. -/
noncomputable def boxSentenceCode (σ : Sentence LAct) (b : V) : V := instB (⌜boxClosed σ⌝ : V) b

/-- The code of `boxClosed σ` is `PlenDer` at `(#0, numeral ⌜σ⌝)` (for a VARIABLE `σ`). -/
theorem quote_boxClosed (σ : Sentence LAct) :
    (⌜boxClosed σ⌝ : V) = subst LAct (^#0 ∷ qNumS σ ∷ 0) PlenDer := by
  rw [boxClosed_def]
  conv_lhs =>
    rw [Sentence.quote_def, Semiformula.coe_subst_eq_subst_coe, Semiformula.quote_def,
      Semiformula.typed_quote_substs, Bootstrapping.Semiformula.val_substs, ← Semiformula.quote_def,
      ← Sentence.quote_def]
  unfold PlenDer lenDerA
  congr 1
  have hv : (fun i ↦ (⌜(Rew.emb (![#0, Semiterm.lMap emb (⌜σ⌝ : ArithmeticSemiterm Empty 1)] i) :
      SyntacticSemiterm LAct 1)⌝ : Bootstrapping.Semiterm V LAct 1)) =
      ![⌜(Rew.emb (#0 : Semiterm LAct Empty 1) : SyntacticSemiterm LAct 1)⌝,
        ⌜(Rew.emb (Semiterm.lMap emb (⌜σ⌝ : ArithmeticSemiterm Empty 1)) : SyntacticSemiterm LAct 1)⌝] := by
    funext i; fin_cases i <;> rfl
  rw [hv]
  simp only [SemitermVec.val_cons, SemitermVec.val_nil, Diag.typed_val_emb, quote_lMap_gödel]
  rfl

/-- **The code equation**: `boxSentenceCode σ b = lenDerFact (bnum b) (numeral ⌜σ⌝)` — the fact the closing
block produces. -/
theorem boxSentenceCode_eq (σ : Sentence LAct) (b : V) :
    boxSentenceCode σ b = lenDerFact (bnum b) (qNumS σ) := by
  unfold boxSentenceCode
  rw [quote_boxClosed, instB]
  have hq : IsSemiterm LAct ((0 : V) + 1) (qNumS σ) :=
    InstV.isSemiterm_LAct_of_LOR (numeral_semiterm ((0 : V) + 1) _)
  have hb : IsSemiterm LAct ((0 : V) + 1) (^#0 : V) := by simp
  have hv : IsSemitermVec LAct ((0 : V) + 1 + 1) ((0 : V) + 1) (^#0 ∷ qNumS σ ∷ (0 : V)) :=
    IsSemitermVec.adjoin (IsSemitermVec.adjoin (IsSemitermVec.nil (L := LAct) ((0 : V) + 1)) hq) hb
  have hw : IsSemitermVec LAct ((0 : V) + 1) (0 : V) (bnum b ∷ (0 : V)) :=
    IsSemitermVec.adjoin (IsSemitermVec.nil (L := LAct) (0 : V)) (bnum_term_LAct b)
  have h2 : ((2 : ℕ) : V) = 0 + 1 + 1 := by simp [one_add_one_eq_two]
  rw [substs_substs (h2 ▸ isSemiformula_PlenDer) hw hv]
  unfold lenDerFact
  congr 1
  rw [termSubstVec_cons hb.isUTerm (IsSemitermVec.adjoin (IsSemitermVec.nil (L := LAct) ((0 : V) + 1)) hq).isUTerm,
    termSubstVec_cons hq.isUTerm (IsSemitermVec.nil (L := LAct) ((0 : V) + 1)).isUTerm, termSubstVec_nil, termSubst_bvar,
    termSubst_eq_self (L := LAct) (w := bnum b ∷ (0 : V)) (isSemiterm_qNumS σ) (fun i hi ↦ by simp at hi)]
  simp

/-- The ℕ reading: at a standard budget `k`, `boxSentenceCode σ k` is the quote of the `LAct`-SENTENCE
`boxClosed σ ⇜ ![bnumT k]` (`InstV.quote_instB`). -/
theorem boxSentenceCode_nat (σ : Sentence LAct) (k : ℕ) :
    boxSentenceCode σ (k : V) = ⌜(boxClosed σ ⇜ ![Semiterm.lMap emb (bnumT k)] : Sentence LAct)⌝ :=
  quote_instB (boxClosed σ) k

lemma isFormula_boxSentenceCode (σ : Sentence LAct) (b : V) : IsFormula LAct (boxSentenceCode σ b) := by
  rw [boxSentenceCode_eq]; exact isFormula_lenDerFact (isSemiterm_bnum_LAct 0 b) (isSemiterm_qNumS σ)

lemma shiftIterV_lenDerFact {a g : V} (ha : IsSemiterm LAct 0 a) (hg : IsSemiterm LAct 0 g) (c : V) :
    shiftIterV (lenDerFact a g) c = lenDerFact (termShiftIterV a c) (termShiftIterV g c) :=
  shiftIterV_fact2 isSemiformula_PlenDer shift_PlenDer ha hg c

/-- The closed target is closed: shifts do not move it. -/
lemma shiftIterV_targetC (σ : Sentence LAct) (b c : V) :
    shiftIterV (lenDerFact (bnum b) (qNumS σ)) c = lenDerFact (bnum b) (qNumS σ) := by
  rw [shiftIterV_lenDerFact (isSemiterm_bnum_LAct 0 b) (isSemiterm_qNumS σ), termShiftIterV_bnumTop,
    termShiftIterV_qNumS]

end closedBox

/-! ## 2. The congruence row `lenDerCong` — `“g' g a. LenDer a g → g = g' → LenDer a g'”`, `m = 3` -/

section congRow

noncomputable def lenDerCongB : ArithmeticSemisentence 3 :=
  “g' g a. !(lenDerivableDef TAct) a g → g = g' → !(lenDerivableDef TAct) a g'”
noncomputable def lenDerCong : ArithmeticSentence := ∀¹* lenDerCongB

lemma models_lenDerCong : V↓[ℒₒᵣ] ⊧ lenDerCong ↔
    ∀ g' g a : V, LenDerivable TAct a g → g = g' → LenDerivable TAct a g' := by
  simp [lenDerCong, lenDerCongB, models_iff, Matrix.vecForall_iff, (LenDerivable.defined (V := V) TAct).iff]

theorem pa_proves_lenDerCong : 𝗣𝗔 ⊢ lenDerCong :=
  Lib.pa_proves_of_models fun _ _ _ ↦ models_lenDerCong.mpr fun _ _ _ h₁ h₂ ↦ h₂ ▸ h₁
theorem lib_lenDerCong : Lib lenDerCong := Lib.of_pa pa_proves_lenDerCong

noncomputable def row_lenDerCong_as : List V :=
  [subst LAct (listToVec [bv 2, bv 1]) PlenDer, subst LAct (listToVec [bv 1, bv 0]) PeqB]
noncomputable def row_lenDerCong_c : V := subst LAct (listToVec [bv 2, bv 0]) PlenDer

theorem quote_row_lenDerCong :
    (⌜Semiformula.lMap emb lenDerCongB⌝ : V) = impChain LAct row_lenDerCong_as row_lenDerCong_c := by
  unfold lenDerCongB row_lenDerCong_as row_lenDerCong_c PlenDer PeqB
  all_goals row_shapeB

lemma isSemiformula_lenDerCong_as : ∀ A ∈ row_lenDerCong_as, IsSemiformula LAct ((3 : ℕ) : V) A := by
  unfold row_lenDerCong_as
  exact (List.forall_mem_cons.mpr ⟨isSemiformula_substRow isSemiformula_PlenDer _ (by rfl) (by row_entriesB),
    List.forall_mem_cons.mpr ⟨isSemiformula_substRow isSemiformula_PeqB _ (by rfl) (by row_entriesB),
    List.forall_mem_nil _⟩⟩)
lemma isSemiformula_lenDerCong_c : IsSemiformula LAct ((3 : ℕ) : V) row_lenDerCong_c := by
  unfold row_lenDerCong_c
  exact isSemiformula_substRow isSemiformula_PlenDer _ (by rfl) (by row_entriesB)

/-- `lenDerCong` at the witnesses `[wa, wg, wg']` (the DSL variables right-to-left). -/
lemma inst_lenDerCong {wa wg wg' : V} (hwa : IsSemiterm LAct 0 wa) (hwg : IsSemiterm LAct 0 wg)
    (hwg' : IsSemiterm LAct 0 wg') :
    row_lenDerCong_as.map (instOuter LAct [wa, wg, wg']) = [lenDerFact wa wg, eqFactB wg wg'] ∧
    instOuter LAct [wa, wg, wg'] row_lenDerCong_c = lenDerFact wa wg' := by
  have hes : ∀ e ∈ ([wa, wg, wg'] : List V), IsSemiterm LAct 0 e :=
    (List.forall_mem_cons.mpr ⟨hwa, List.forall_mem_cons.mpr ⟨hwg, List.forall_mem_cons.mpr ⟨hwg', List.forall_mem_nil _⟩⟩⟩)
  unfold row_lenDerCong_as row_lenDerCong_c
  simp only [List.map_cons, List.map_nil]
  rw [instOuter_subst_listToVec _ isSemiformula_PlenDer (by rfl) _ hes (by row_entriesB),
    instOuter_subst_listToVec _ isSemiformula_PeqB (by rfl) _ hes (by row_entriesB),
    instOuter_subst_listToVec _ isSemiformula_PlenDer (by rfl) _ hes (by row_entriesB)]
  all_goals try row_entries_simpB
  row_finish

end congRow

/-! ## 3. The extended table: `indRecRows ++ [lenDerCong]` -/

section closedTable

noncomputable def lenDerCongRow : WRow := ⟨3, lenDerCongB, lib_lenDerCong⟩

/-- The `IndRec` rows followed by the congruence row. -/
noncomputable def closedRows : List WRow := indRecRows ++ [lenDerCongRow]

/-- The index of the congruence row. -/
def cIdx : ℕ := indRecRowCount

lemma closedRows_length : closedRows.length = cIdx + 1 := by
  simp [closedRows, indRecRows_length, cIdx]

lemma closedRows_getElem_of_lt {i : ℕ} (h : i < indRecRows.length) (hc : i < closedRows.length) :
    closedRows[i]'hc = indRecRows[i]'h := by
  apply Option.some.inj
  rw [← List.getElem?_eq_getElem hc, ← List.getElem?_eq_getElem h]
  exact List.getElem?_append_left h

/-- The row at `cIdx` is the congruence row (stated for a VARIABLE index: a closed `getElem` index makes the
elaborator walk the whole list). -/
lemma closedRows_getElem_cIdx {i : ℕ} (hi : i = cIdx) (hc : i < closedRows.length) :
    closedRows[i]'hc = lenDerCongRow := by
  apply Option.some.inj
  rw [← List.getElem?_eq_getElem hc]
  unfold closedRows
  rw [List.getElem?_append_right (by rw [indRecRows_length, hi]; exact le_rfl)]
  simp [hi, cIdx, indRecRows_length]

/-- **The closed table**: an `IndRec` table whose row `cIdx` is the congruence row. -/
def ClosedTable (tbl : V) : Prop :=
  IndRecTable tbl ∧ ((cIdx : ℕ) : V) < len tbl ∧
  rowM tbl.[((cIdx : ℕ) : V)] = ((3 : ℕ) : V) ∧
  rowB tbl.[((cIdx : ℕ) : V)] = ⌜Semiformula.lMap emb lenDerCongB⌝

lemma ClosedTable.indRecTable {tbl : V} (h : ClosedTable tbl) : IndRecTable tbl := h.1
lemma ClosedTable.topTable {tbl : V} (h : ClosedTable tbl) : TopTable tbl := h.1.proTable.topTable
lemma ClosedTable.proTable {tbl : V} (h : ClosedTable tbl) : ProTable tbl := h.1.proTable

/-- **A closed table with its row-body bound exists in every model** (`Assemble.exists_indRecTableB` at
`closedRows`). -/
theorem exists_closedTableB : ∃ N B : ℕ, ∀ (V : Type) [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁],
    ∃ tbl : V, TableOK tbl (N : V) ∧ ClosedTable tbl ∧ ∀ j < len tbl, formulaLen LAct (rowB tbl.[j]) ≤ (B : V) := by
  obtain ⟨N, hN⟩ := exists_rows closedRows
  refine ⟨N, rowsB closedRows, fun V _ _ ↦ ?_⟩
  obtain ⟨rows, hlen, hok, hidx⟩ := hN V
  have hcI : cIdx < closedRows.length := by rw [closedRows_length]; exact Nat.lt_succ_self _
  have hcI' : cIdx < rows.length := by rw [hlen]; exact hcI
  refine ⟨vecOf rows, tableOK_vecOf rows hok, ⟨⟨?_, ?_⟩, ?_, ?_, ?_⟩, ?_⟩
  · rw [len_vecOf, hlen, closedRows_length]; exact_mod_cast Nat.le_succ _
  · intro i h
    have hc : i < closedRows.length := by
      rw [closedRows_length]; exact Nat.lt_succ_of_lt (by rw [indRecRows_length] at h; exact h)
    have h' : i < rows.length := by rw [hlen]; exact hc
    rw [nth_vecOf rows i h']
    have := hidx i hc h'
    rwa [closedRows_getElem_of_lt h hc] at this
  · rw [len_vecOf, hlen, closedRows_length]; exact_mod_cast Nat.lt_succ_self _
  · rw [nth_vecOf rows cIdx hcI', (hidx cIdx hcI hcI').1, closedRows_getElem_cIdx rfl hcI]; rfl
  · rw [nth_vecOf rows cIdx hcI', (hidx cIdx hcI hcI').2, closedRows_getElem_cIdx rfl hcI]; rfl
  · intro j hj
    rw [len_vecOf] at hj
    obtain ⟨i, rfl⟩ := eq_nat_of_lt_nat hj
    have h' : i < rows.length := by exact_mod_cast hj
    have h : i < closedRows.length := by rw [← hlen]; exact h'
    rw [nth_vecOf rows i h', (hidx i h h').2, ← Sentence.coe_quote_eq_quote (V := V), flN_cast]
    exact_mod_cast flN_le_rowsB closedRows i h

/-- The congruence step (a plain Horn step at row `cIdx`; no piece table needed). -/
noncomputable def stepLenDerCong (wa wg wg' : V) : V :=
  sUseHorn ((cIdx : ℕ) : V) (vecOf [wa, wg, wg']) (vecOf row_lenDerCong_as) row_lenDerCong_c

/-- Row `lenDerCong` as a step. -/
lemma tok_lenDerCong {tbl N E Γ : V} {wa wg wg' : V} (htbl : TableOK tbl N) (hC : ClosedTable tbl)
    (hΓ : IsFormulaSet LAct Γ) (hwa : IsSemiterm LAct 0 wa) (hEwa : termLen LAct wa ≤ E)
    (hwg : IsSemiterm LAct 0 wg) (hEwg : termLen LAct wg ≤ E) (hwg' : IsSemiterm LAct 0 wg')
    (hEwg' : termLen LAct wg' ≤ E) (hmem0 : neg LAct (lenDerFact wa wg) ∈ Γ) (hmem1 : neg LAct (eqFactB wg wg') ∈ Γ) :
    StepOK tbl E ((8 : ℕ) : V) Γ (stepLenDerCong wa wg wg') ∧ sTag (stepLenDerCong wa wg wg') = 0 ∧
    ctxAfter Γ (stepLenDerCong wa wg wg') = insert (neg LAct (lenDerFact wa wg')) Γ := by
  have hes : ∀ e ∈ [wa, wg, wg'], IsSemiterm LAct 0 e ∧ termLen LAct e ≤ E :=
    List.forall_mem_cons.mpr ⟨⟨hwa, hEwa⟩, List.forall_mem_cons.mpr ⟨⟨hwg, hEwg⟩,
      List.forall_mem_cons.mpr ⟨⟨hwg', hEwg'⟩, List.forall_mem_nil _⟩⟩⟩
  have hinst := inst_lenDerCong hwa hwg hwg'
  have hrowB : rowB tbl.[((cIdx : ℕ) : V)] = impChainV LAct (vecOf row_lenDerCong_as) row_lenDerCong_c := by
    rw [impChainV_vecOf, hC.2.2.2, quote_row_lenDerCong]
  unfold stepLenDerCong
  refine ⟨stepOK_useHorn htbl [wa, wg, wg'] row_lenDerCong_as hΓ hC.2.1 hC.2.2.1 hrowB
    (by exact_mod_cast (by decide : 3 ≤ 8))
    (by rw [show row_lenDerCong_as.length = 2 from rfl]; exact_mod_cast (by decide : 2 ≤ 8)) hes ?_, by simp, ?_⟩
  · exact neg_mem_of_map hinst.1 (List.forall_mem_cons.mpr ⟨hmem0, List.forall_mem_cons.mpr ⟨hmem1, List.forall_mem_nil _⟩⟩)
  · rw [ctxAfter_useHorn [wa, wg, wg'] row_lenDerCong_as isSemiformula_lenDerCong_c (fun e he ↦ (hes e he).1), hinst.2]

end closedTable

/-! ## 4. The closing block: `goalElim`, ONE numeral lemma, four top rows, the congruence -/

section closeStepsC

/-- `closeStepsC σ b ρ js tblN`: with the root goal fact `goalFact (^&js) (bnum (dlen ρ))`, the chain fact
`insFact &js &(js+1) 𝟎` and the pinned `eqFact &(js+1) (numeral ⌜σ⌝)` in context — `goalElim` (2 shifts:
`d = &1`, `n = &0`, the sequent at `&(js+2)`, the member at `&(js+3)`), then the numeral lemma
`dlen ρ ≤ b` (N2), `dlenDefIntro [&1, &0]`, `proofIntro [&(js+2), &(js+3), &1]`, `leTrans [bnum b, bnum (dlen ρ), &0]`,
`lenDerIntro [&1, &0, &(js+3), bnum b]`, `lenDerCong [bnum b, &(js+3), numeral ⌜σ⌝]` — whose conclusion is the
closed target `lenDerFact (bnum b) (numeral ⌜σ⌝)`. `11` steps, `2` shifts. -/
noncomputable def closeStepsC (σ : Sentence LAct) (b ρ js tblN : V) : V :=
  appendV (goalElim (^&js) (bnum (dlen TAct ρ)))
    (sLemma (leFact (bnum (dlen TAct ρ)) (bnum b)) (leCode tblN (dlen TAct ρ) b) ∷
     mkStep topPieces 150 ?[^&1, ^&0] ∷
     mkStep topPieces 151 ?[^&(js + 2), ^&(js + 3), ^&1] ∷
     mkStep topPieces 110 ?[bnum b, bnum (dlen TAct ρ), ^&0] ∷
     mkStep topPieces 153 ?[^&1, ^&0, ^&(js + 3), bnum b] ∷
     stepLenDerCong (bnum b) (^&(js + 3)) (qNumS σ) ∷ (0 : V))

/-- **The closing steps are applicable** and end with the closed target: cap `8`, cut-admitting, `2` shifts,
`11` steps. -/
theorem closeStepsC_ok (σ : Sentence LAct) {tbl N E Γ tblN N' B' b ρ js : V}
    (htbl : TableOK tbl N) (hC : ClosedTable tbl) (htblN : NumTableOK tblN N' B')
    (hΓ : IsFormulaSet LAct Γ) (hρ : dlen TAct ρ ≤ b)
    (hE1 : js + 4 ≤ E) (hEq : termLen LAct (qNumS σ : V) ≤ E) (hEb : termLen LAct (bnum b) ≤ E)
    (hEd : termLen LAct (bnum (dlen TAct ρ)) ≤ E)
    (hgoal : neg LAct (goalFact (^&js) (bnum (dlen TAct ρ))) ∈ Γ)
    (hins : neg LAct (insFact (^&js) (^&(js + 1)) (𝟎 : V)) ∈ Γ)
    (hpin : neg LAct (eqFactB (^&(js + 1)) (qNumS σ)) ∈ Γ) :
    ListOK tbl E ((8 : ℕ) : V) Γ (closeStepsC σ b ρ js tblN) ∧
    NoDrop' (closeStepsC σ b ρ js tblN) ∧ shiftsV (closeStepsC σ b ρ js tblN) = 2 ∧
    len (closeStepsC σ b ρ js tblN) = 11 ∧
    neg LAct (lenDerFact (bnum b) (qNumS σ)) ∈ finalCtx Γ (closeStepsC σ b ρ js tblN) := by
  have hT : TopTable tbl := hC.topTable
  have h0 : IsSemiterm LAct (0 : V) (𝟎 : V) := isSemiterm_qqZero_LAct 0
  have hq : IsSemiterm LAct (0 : V) (qNumS σ) := isSemiterm_qNumS σ
  have hbb : IsSemiterm LAct (0 : V) (bnum b) := isSemiterm_bnum_LAct 0 b
  have hbd : IsSemiterm LAct (0 : V) (bnum (dlen TAct ρ)) := isSemiterm_bnum_LAct 0 _
  have hE4 : (4 : V) ≤ E := le_trans le_add_self hE1
  have hf0 : termLen LAct (^&0 : V) ≤ E := termLen_fvar_le (le_trans (by norm_num) hE4)
  have hf1 : termLen LAct (^&1 : V) ≤ E := termLen_fvar_le (le_trans (by norm_num) hE4)
  have hf2 : termLen LAct (^&(js + 2) : V) ≤ E := termLen_fvar_le (by
    calc js + 2 + 1 = js + 3 := by ring
      _ ≤ js + 4 := add_le_add le_rfl (by norm_num)
      _ ≤ E := hE1)
  have hf3 : termLen LAct (^&(js + 3) : V) ≤ E := termLen_fvar_le (by
    calc js + 3 + 1 = js + 4 := by ring
      _ ≤ E := hE1)
  have e2 : (js : V) + 1 + 1 = js + 2 := by rw [add_assoc, one_add_one_eq_two]
  have e3 : (js : V) + 1 + 2 = js + 3 := by rw [add_assoc]; norm_num
  -- the recovery of the goal
  obtain ⟨gok, gnd, gsh, _, gder, gfst, gdlen, gle⟩ := goalElim_ok 8 htbl hΓ (by simp) hbd hgoal
  rw [termShift_fvar, termShift_fvar, e2] at gfst
  rw [termShift_bnum, termShift_bnum] at gle
  have hΓ₀ : IsFormulaSet LAct (finalCtx Γ (goalElim (^&js) (bnum (dlen TAct ρ)))) :=
    finalCtx_isFormulaSet 8 htbl hΓ gok
  have hins₀ := mem_finalCtx_of_mem' gnd hins
  rw [gsh, shiftIterV_neg (isFormula_insFact (by simp) (by simp) h0), shiftIterV_insFact (by simp) (by simp) h0,
    termShiftIterV_fvar, termShiftIterV_fvar, termShiftIterV_qqZero, e3] at hins₀
  have hpin₀ := mem_finalCtx_of_mem' gnd hpin
  rw [gsh, shiftIterV_neg (isFormula_eqFactB (by simp) hq), shiftIterV_eqFactB (by simp) hq,
    termShiftIterV_fvar, termShiftIterV_qNumS, e3] at hpin₀
  set Γ₀ := finalCtx Γ (goalElim (^&js) (bnum (dlen TAct ρ))) with hΓ₀def
  -- the numeral lemma N2
  have ok₁ : StepOK tbl E ((8 : ℕ) : V) Γ₀
      (sLemma (leFact (bnum (dlen TAct ρ)) (bnum b)) (leCode tblN (dlen TAct ρ) b)) :=
    stepOK_sLemma hΓ₀ (lemmaOK_of (isFormula_leFact_bnum _ _) (leCode_proof htblN hρ))
  have cx₁ := ctxAfter_sLemma Γ₀ (leFact (bnum (dlen TAct ρ)) (bnum b)) (leCode tblN (dlen TAct ρ) b)
  set Γ₁ := insert (neg LAct (leFact (bnum (dlen TAct ρ)) (bnum b))) Γ₀ with hΓ₁def
  have hΓ₁ : IsFormulaSet LAct Γ₁ := cx₁ ▸ isFormulaSet_ctxAfter 8 htbl ok₁
  -- the facts so far, in `Γ₁`
  have m_der : neg LAct (derFact (^&1 : V)) ∈ Γ₁ := mem_ins gder
  have m_fst : neg LAct (fstIdxFact (^&(js + 2)) (^&1)) ∈ Γ₁ := mem_ins gfst
  have m_dlen : neg LAct (dlenFact (^&1 : V) (^&0)) ∈ Γ₁ := mem_ins gdlen
  have m_le : neg LAct (leFact (^&0) (bnum (dlen TAct ρ))) ∈ Γ₁ := mem_ins gle
  have m_ins : neg LAct (insFact (^&(js + 2)) (^&(js + 3)) (𝟎 : V)) ∈ Γ₁ := mem_ins hins₀
  have m_pin : neg LAct (eqFactB (^&(js + 3)) (qNumS σ)) ∈ Γ₁ := mem_ins hpin₀
  have m_leb : neg LAct (leFact (bnum (dlen TAct ρ)) (bnum b)) ∈ Γ₁ := by rw [hΓ₁def]; simp
  -- step 2: dlenDefIntro
  obtain ⟨ok₂, tg₂, cx₂⟩ := tok_dlenDefIntro (wd := ^&1) (wn := ^&0) htbl hT rfl hΓ₁ (by simp) hf1 (by simp) hf0 m_der m_dlen
  set Γ₂ := insert (neg LAct (dlenDefFact (^&0) (^&1))) Γ₁ with hΓ₂def
  have hΓ₂ : IsFormulaSet LAct Γ₂ := cx₂ ▸ isFormulaSet_ctxAfter 8 htbl ok₂
  -- step 3: proofIntro
  obtain ⟨ok₃, tg₃, cx₃⟩ := tok_proofIntro (ws := ^&(js + 2)) (wg := ^&(js + 3)) (wd := ^&1) htbl hT rfl hΓ₂
    (by simp) hf2 (by simp) hf3 (by simp) hf1 (mem_ins m_ins) (mem_ins m_fst) (mem_ins m_der)
  set Γ₃ := insert (neg LAct (proofFact (^&1) (^&(js + 3)))) Γ₂ with hΓ₃def
  have hΓ₃ : IsFormulaSet LAct Γ₃ := cx₃ ▸ isFormulaSet_ctxAfter 8 htbl ok₃
  -- step 4: leTrans
  obtain ⟨ok₄, tg₄, cx₄⟩ := tfok_leTrans (wz := bnum b) (wy := bnum (dlen TAct ρ)) (wx := ^&0) htbl hT rfl hΓ₃
    hbb hEb hbd hEd (by simp) hf0 (mem_ins (mem_ins m_le)) (mem_ins (mem_ins m_leb))
  set Γ₄ := insert (neg LAct (leFact (^&0) (bnum b))) Γ₃ with hΓ₄def
  have hΓ₄ : IsFormulaSet LAct Γ₄ := cx₄ ▸ isFormulaSet_ctxAfter 8 htbl ok₄
  -- step 5: lenDerIntro
  obtain ⟨ok₅, tg₅, cx₅⟩ := tok_lenDerIntro (wd := ^&1) (wn := ^&0) (wg := ^&(js + 3)) (wa := bnum b) htbl hT rfl hΓ₄
    (by simp) hf1 (by simp) hf0 (by simp) hf3 hbb hEb (mem_ins (by rw [hΓ₃def]; simp))
    (mem_ins (mem_ins (by rw [hΓ₂def]; simp))) (by rw [hΓ₄def]; simp)
  set Γ₅ := insert (neg LAct (lenDerFact (bnum b) (^&(js + 3)))) Γ₄ with hΓ₅def
  have hΓ₅ : IsFormulaSet LAct Γ₅ := cx₅ ▸ isFormulaSet_ctxAfter 8 htbl ok₅
  -- step 6: lenDerCong
  obtain ⟨ok₆, tg₆, cx₆⟩ := tok_lenDerCong (wa := bnum b) (wg := ^&(js + 3)) (wg' := qNumS σ) htbl hC hΓ₅
    hbb hEb (by simp) hf3 hq hEq (by rw [hΓ₅def]; simp) (mem_ins (mem_ins (mem_ins (mem_ins m_pin))))
  -- assembly
  have hfin : finalCtx Γ (closeStepsC σ b ρ js tblN) = insert (neg LAct (lenDerFact (bnum b) (qNumS σ))) Γ₅ := by
    unfold closeStepsC
    rw [finalCtx_appendV, ← hΓ₀def, finalCtx_cons, cx₁, finalCtx_cons, cx₂, finalCtx_cons, cx₃,
      finalCtx_cons, cx₄, finalCtx_cons, cx₅, finalCtx_single, cx₆]
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · unfold closeStepsC
    refine listOK_appendV gok ?_
    rw [← hΓ₀def]
    refine listOK_cons ok₁ ?_; rw [cx₁]
    refine listOK_cons ok₂ ?_; rw [cx₂]
    refine listOK_cons ok₃ ?_; rw [cx₃]
    refine listOK_cons ok₄ ?_; rw [cx₄]
    refine listOK_cons ok₅ ?_; rw [cx₅]
    exact listOK_single ok₆
  · unfold closeStepsC
    refine noDrop'_appendV gnd ?_
    exact noDrop'_cons (by simp) (noDrop'_cons (by rw [tg₂]; simp) (noDrop'_cons (by rw [tg₃]; simp)
      (noDrop'_cons (by rw [tg₄]; simp) (noDrop'_cons (by rw [tg₅]; simp) (noDrop'_single (by rw [tg₆]; simp))))))
  · unfold closeStepsC
    rw [shiftsV_appendV, gsh, shiftsV_cons, shiftsV_cons, shiftsV_cons, shiftsV_cons, shiftsV_cons, shiftsV_single,
      tg₂, tg₃, tg₄, tg₅, tg₆]
    simp
  · unfold closeStepsC
    rw [len_appendV, len_goalElim]; simp [len_adjoin]; norm_num
  · rw [hfin]; simp

end closeStepsC

/-! ## 5. The top: the witness cap, the list, the derivation, the explicit bound -/

section topC

/-- The walk of the root member `⌜σ⌝` (`rootSteps_ok`): a CONSTANT of `σ`. -/
noncomputable def eWalkC (σ : Sentence LAct) : V := 2 * formulaLen LAct (⌜σ⌝ : V) + 8
/-- The pin (`numId_sentence`) at offset `0 + 2`. -/
noncomputable def ePinC (Cσ : ℕ) : V := (Cσ : V) + (0 + 2)
/-- The verify kit at offset `0` (the pin is shift-free). -/
noncomputable def eVerC (d : V) (Ck : ℕ) (m : ℕ) : V := (Ck : V) * ((d + 1) ^ m + (0 + 0))
/-- The closing block's indices: `js + 4` with `js = 0 + 0 + 1 + σ`, `σ ≤ Ck(d+1)^m`. -/
noncomputable def eJsC (d : V) (Ck : ℕ) (m : ℕ) : V := 0 + 0 + 1 + (Ck : V) * (d + 1) ^ m + 4
noncomputable def eQC (σ : Sentence LAct) : V := termLen LAct (qNumS σ : V)

/-- **The witness cap of the closed top**: seven requirements (`eK b`, `eD d` are `Top.lean`'s). -/
noncomputable def EtopC (σ : Sentence LAct) (b d : V) (Ck Cσ : ℕ) (m : ℕ) : V :=
  eWalkC σ + ePinC Cσ + eVerC d Ck m + eJsC d Ck m + eQC σ + eK b + eD d

lemma le_EtopC_walk (σ : Sentence LAct) (b d : V) (Ck Cσ : ℕ) (m : ℕ) : eWalkC σ ≤ EtopC σ b d Ck Cσ m := by
  unfold EtopC; exact le_trans (le_trans (le_trans (le_trans (le_trans (le_self_add) le_self_add) le_self_add) le_self_add) le_self_add) le_self_add
lemma le_EtopC_pin (σ : Sentence LAct) (b d : V) (Ck Cσ : ℕ) (m : ℕ) : ePinC Cσ ≤ EtopC σ b d Ck Cσ m := by
  unfold EtopC; exact le_trans (le_trans (le_trans (le_trans (le_trans (le_add_self) le_self_add) le_self_add) le_self_add) le_self_add) le_self_add
lemma le_EtopC_ver (σ : Sentence LAct) (b d : V) (Ck Cσ : ℕ) (m : ℕ) : eVerC d Ck m ≤ EtopC σ b d Ck Cσ m := by
  unfold EtopC; exact le_trans (le_trans (le_trans (le_trans (le_add_self) le_self_add) le_self_add) le_self_add) le_self_add
lemma le_EtopC_js (σ : Sentence LAct) (b d : V) (Ck Cσ : ℕ) (m : ℕ) : eJsC d Ck m ≤ EtopC σ b d Ck Cσ m := by
  unfold EtopC; exact le_trans (le_trans (le_trans (le_add_self) le_self_add) le_self_add) le_self_add
lemma le_EtopC_q (σ : Sentence LAct) (b d : V) (Ck Cσ : ℕ) (m : ℕ) : eQC σ ≤ EtopC σ b d Ck Cσ m := by
  unfold EtopC; exact le_trans (le_trans (le_add_self) le_self_add) le_self_add
lemma le_EtopC_k (σ : Sentence LAct) (b d : V) (Ck Cσ : ℕ) (m : ℕ) : eK b ≤ EtopC σ b d Ck Cσ m := by
  unfold EtopC; exact le_trans (le_add_self) le_self_add
lemma le_EtopC_d (σ : Sentence LAct) (b d : V) (Ck Cσ : ℕ) (m : ℕ) : eD d ≤ EtopC σ b d Ck Cσ m := by
  unfold EtopC; exact le_add_self

/-- The witness cap plus the E-room of the certificate table (the second summand of `Assemble.Etop` at three
primes). -/
noncomputable def EtopCv (σ : Sentence LAct) (b d : V) (Ck Cσ Cv : ℕ) (m : ℕ) : V :=
  EtopC σ b d Ck Cσ m + ((Cv : V) * p3 (d + 1) + 6 * d + 1)

lemma le_EtopCv_top (σ : Sentence LAct) (b d : V) (Ck Cσ Cv : ℕ) (m : ℕ) :
    EtopC σ b d Ck Cσ m ≤ EtopCv σ b d Ck Cσ Cv m := le_self_add
lemma le_EtopCv_axm (σ : Sentence LAct) (b d : V) (Ck Cσ Cv : ℕ) (m : ℕ) :
    (Cv : V) * p3 (d + 1) + 6 * d + 1 ≤ EtopCv σ b d Ck Cσ Cv m := le_add_self

/-- The one `sLemma` derivation of the closed closing block (`NumSteps.dlen_leCode_le` with the addition). -/
noncomputable def closeD (N' B' b d : V) : V :=
  (‖d‖ + 1) * (‖b‖ + 2) * nodeCost N' B' (12 * ‖b‖ + 3) + nodeCost N' B' (12 * ‖b‖ + 3)

/-- The top list for a pin list `P` and a verification list `L`. -/
noncomputable def topListC (σ : Sentence LAct) (b ρ P L tblN : V) : V :=
  appendV (rootSteps (⌜σ⌝ : V))
    (appendV P (appendV L (closeStepsC σ b ρ (0 + shiftsV P + 1 + shiftsV L) tblN)))

/-- **The closed top, assembled**: from a proof code `ρ` of `⌜σ⌝` with `dlen ρ ≤ b`, the verification graph
and the certificate table at the cap `E ≥ EtopC`, a `TAct`-derivation of the closed box code of length
`≤ topBound''` at `lk = 0` — the FOUR blocks (root walk, `numId` pin, verification list, closing block), the
leaf `axL` on the target, and the cost accounting of `Assemble.top_main'''` with the pin's and the closing
block's shapes re-derived. -/
theorem top_mainC (σ : Sentence LAct) (m : ℕ) {tbl N B Wl Wc W₁ W₂ W tN A N' B' : V} {Ck Cσ Cv : ℕ}
    (htbl : TableOK tbl N) (hC : ClosedTable tbl) (hB : ∀ j < len tbl, formulaLen LAct (rowB tbl.[j]) ≤ B)
    (hPle : formulaLen LAct (Ple : V) ≤ B) (htblN : NumTableOK tN N' B')
    (hkit : VerifyKit''' tbl N B Wl Wc W₁ W₂ W tN Cv Ck m)
    (hpin : ∀ {Γ i E : V}, IsFormulaSet LAct Γ → DossF walkPieces Γ 0 (⌜σ⌝ : V) i → (Cσ : V) + i ≤ E →
      ∃ P : V, NumInv tbl E Γ Cσ P (eqFact (^&i) (numeral (⌜σ⌝ : V))))
    {b ρ : V} (hρ : Proof TAct ρ (⌜σ⌝ : V)) (hlen : dlen TAct ρ ≤ b)
    {L E : V} (hL : VerifyGraph'' walkPieces Wl Wc W₁ W₂ W tN A ρ L) (hA : AxmTableOK' tbl E walkPieces A (Cv : V))
    (hE : EtopC σ b (dlen TAct ρ) Ck Cσ m ≤ E) :
    ∃ e Lr : V, LenDerivable TAct e (boxSentenceCode σ b) ∧
      Lr + 4 ≤ 12 * formulaLen LAct (⌜σ⌝ : V) + 13 ∧
      e ≤ topBound'' N B E Ck Cσ 0 (dlen TAct ρ) (setLen LAct (insert (lenDerFact (bnum b) (qNumS σ)) (∅ : V)))
        (fvOccS LAct (insert (lenDerFact (bnum b) (qNumS σ)) (∅ : V))) Lr (closeD N' B' b (dlen TAct ρ)) m := by
  have hT : TopTable tbl := hC.topTable
  obtain ⟨x, hxdef⟩ : ∃ x, x = (⌜σ⌝ : V) := ⟨_, rfl⟩
  obtain ⟨T, hTdef⟩ : ∃ T, T = lenDerFact (bnum b) (qNumS σ) := ⟨_, rfl⟩
  obtain ⟨Γ₀, hΓ₀def⟩ : ∃ Γ₀ : V, Γ₀ = insert T (∅ : V) := ⟨_, rfl⟩
  rw [← hxdef] at hρ ⊢
  rw [← hTdef, ← hΓ₀def]
  have hx : IsSemiformula LAct 0 x := hxdef ▸ Sentence.quote_isSemiformula₀ σ
  have hq : IsSemiterm LAct (0 : V) (qNumS σ) := isSemiterm_qNumS σ
  have hq' : IsSemiterm LAct (0 : V) (numeral (⌜σ⌝ : V)) := hq
  have hbb : IsSemiterm LAct (0 : V) (bnum b) := isSemiterm_bnum_LAct 0 b
  have hTf : IsFormula LAct T := hTdef ▸ isFormula_lenDerFact hbb hq
  have hΓ₀ : IsFormulaSet LAct Γ₀ := hΓ₀def ▸ IsFormulaSet.insert_iff.mpr ⟨hTf, IsFormulaSet.empty⟩
  have hTmem : T ∈ Γ₀ := by rw [hΓ₀def]; simp
  -- the cap requirements, read off `EtopC`
  have r_walk : eWalkC σ ≤ E := le_trans (le_EtopC_walk σ b (dlen TAct ρ) Ck Cσ m) hE
  have r_pin : ePinC Cσ ≤ E := le_trans (le_EtopC_pin σ b (dlen TAct ρ) Ck Cσ m) hE
  have r_ver : eVerC (dlen TAct ρ) Ck m ≤ E := le_trans (le_EtopC_ver σ b (dlen TAct ρ) Ck Cσ m) hE
  have r_js : eJsC (dlen TAct ρ) Ck m ≤ E := le_trans (le_EtopC_js σ b (dlen TAct ρ) Ck Cσ m) hE
  have r_q : eQC σ ≤ E := le_trans (le_EtopC_q σ b (dlen TAct ρ) Ck Cσ m) hE
  have r_b : eK b ≤ E := le_trans (le_EtopC_k σ b (dlen TAct ρ) Ck Cσ m) hE
  have r_d : eD (dlen TAct ρ) ≤ E := le_trans (le_EtopC_d σ b (dlen TAct ρ) Ck Cσ m) hE
  unfold eWalkC at r_walk
  rw [← hxdef] at r_walk
  unfold ePinC at r_pin
  unfold eVerC at r_ver
  unfold eJsC at r_js
  unfold eQC at r_q
  unfold eK at r_b
  unfold eD at r_d
  have hE1 : (1 : V) ≤ E := le_trans (by norm_num) (le_trans le_add_self r_walk)
  -- (1) the root block
  obtain ⟨rok, rnd, rho, rsh, rlen, rlay⟩ := rootSteps_ok htbl hT hx hΓ₀ r_walk
  set Γ₁ := finalCtx Γ₀ (rootSteps x) with hΓ₁def
  have hΓ₁ : IsFormulaSet LAct Γ₁ := finalCtx_isFormulaSet 8 htbl hΓ₀ rok
  have rB : ∀ i < len (rootSteps x), formulaLen LAct (rowB tbl.[sRow (rootSteps x).[i]]) ≤ B :=
    fun i hi ↦ hB _ (sRow_lt_of_stepOK (rok i hi) (rho i hi))
  have rcost := costSum_le_of_hornOnly hE1 htbl rok rho rB
  obtain ⟨rF, rS⟩ := ctxVec_len_le hE1 htbl rok rho rB (len (rootSteps x)) le_rfl
  have rF' : fvOccS LAct Γ₁ ≤ topF1 B E (fvOccS LAct Γ₀) (len (rootSteps x)) := rF
  have rS' : setLen LAct Γ₁ ≤ topS1 B E (setLen LAct Γ₀) (fvOccS LAct Γ₀) (len (rootSteps x)) := rS
  -- (2) the pin block (`numId` on the root dossier)
  obtain ⟨P, pok, pnd, psh, plen, psz, pinst⟩ := hpin hΓ₁ (hxdef ▸ rlay.1) r_pin
  set Γ₂ := finalCtx Γ₁ P with hΓ₂def
  have hΓ₂ : IsFormulaSet LAct Γ₂ := finalCtx_isFormulaSet 9 htbl hΓ₁ pok
  have lay₂ : RootLayout Γ₂ x (0 + shiftsV P) := rlay.transport pnd
  have pcost := numInv_cost hE1 htbl hB ⟨pok, pnd, psh, plen, psz, pinst⟩
  obtain ⟨pF, pS⟩ := ctxVec_len_le_sizeOK 9 hE1 htbl hB pok psz (len P) le_rfl
  have pF' : fvOccS LAct Γ₂ ≤ fvOccS LAct Γ₁ + len P * growK B E (Cσ : V) := pF
  have pS' : setLen LAct Γ₂ ≤ setLen LAct Γ₁ + len P * fvOccS LAct Γ₁ + (len P * len P + len P) * growK B E (Cσ : V) := pS
  -- (3) the verification block
  have r_ver' : (Ck : V) * ((dlen TAct ρ + 1) ^ m + (0 + shiftsV P)) ≤ E := by rw [psh]; exact r_ver
  obtain ⟨vok, vnd, vsh, vgoal⟩ := hkit.ok hρ hx lay₂ hΓ₂ r_ver' hA hL
  obtain ⟨vcost, vS, vF⟩ := hkit.cost hρ hx lay₂ hΓ₂ r_ver' hA hL
  obtain ⟨L₁, hL₁⟩ : ∃ L₁, L₁ = vList Wl Wc W tN x (0 + shiftsV P) ρ L := ⟨_, rfl⟩
  rw [← hL₁] at vok vnd vsh vgoal vcost vS vF
  set Γ₃ := finalCtx Γ₂ L₁ with hΓ₃def
  have hΓ₃ : IsFormulaSet LAct Γ₃ := finalCtx_isFormulaSet 9 htbl hΓ₂ vok
  have lay₃ : RootLayout Γ₃ x (0 + shiftsV P + shiftsV L₁) := lay₂.transport vnd
  set js := 0 + shiftsV P + 1 + shiftsV L₁ with hjsdef
  have hins₃ : neg LAct (insFact (^&js) (^&(js + 1)) (𝟎 : V)) ∈ Γ₃ := by
    have := lay₃.2.2.1
    have e1 : (0 : V) + shiftsV P + shiftsV L₁ + 1 = js := by rw [hjsdef]; ring
    have e2 : (0 : V) + shiftsV P + shiftsV L₁ + 2 = js + 1 := by rw [hjsdef]; ring
    rwa [e1, e2] at this
  have hpin₃ : neg LAct (eqFactB (^&(js + 1)) (qNumS σ)) ∈ Γ₃ := by
    have := mem_finalCtx_of_mem' vnd pinst
    rw [eqFact_eq_eqFactB, shiftIterV_neg (isFormula_eqFactB (by simp) hq'), shiftIterV_eqFactB (by simp) hq',
      termShiftIterV_fvar, termShiftIterV_numeral] at this
    have e : (0 : V) + 2 + shiftsV L₁ = js + 1 := by rw [hjsdef, psh]; ring
    rw [e] at this
    exact this
  -- (4) the closing block
  have r_js' : js + 4 ≤ E := by
    refine le_trans ?_ r_js
    rw [hjsdef, psh]
    exact add_le_add (add_le_add le_rfl vsh) le_rfl
  obtain ⟨cok, cnd, csh, clen, cT⟩ := closeStepsC_ok σ htbl hC htblN hΓ₃ hlen r_js' r_q r_b r_d vgoal hins₃ hpin₃
  set Γ₄ := finalCtx Γ₃ (closeStepsC σ b ρ js tN) with hΓ₄def
  have hΓ₄ : IsFormulaSet LAct Γ₄ := finalCtx_isFormulaSet 8 htbl hΓ₃ cok
  -- the whole list
  set S := topListC σ b ρ P L₁ tN with hSdef
  have h89 : ((8 : ℕ) : V) ≤ ((9 : ℕ) : V) := by exact_mod_cast (by decide : (8 : ℕ) ≤ 9)
  have hSfin : finalCtx Γ₀ S = Γ₄ := by
    rw [hSdef, topListC, ← hxdef, ← hjsdef, finalCtx_appendV, finalCtx_appendV, finalCtx_appendV, ← hΓ₁def,
      ← hΓ₂def, ← hΓ₃def]
  have hok : ListOK tbl E ((9 : ℕ) : V) Γ₀ S := by
    rw [hSdef, topListC, ← hxdef, ← hjsdef]
    refine listOK_appendV (rok.mono h89) ?_
    rw [← hΓ₁def]
    refine listOK_appendV pok ?_
    rw [← hΓ₂def]
    refine listOK_appendV vok ?_
    rw [← hΓ₃def]
    exact cok.mono h89
  have hnd : NoDrop' S := by
    rw [hSdef, topListC, ← hxdef, ← hjsdef]
    exact noDrop'_appendV rnd.noDrop' (noDrop'_appendV pnd (noDrop'_appendV vnd cnd))
  have hT₄ : T ∈ Γ₄ := by
    have := mem_finalCtx_of_mem' hnd hTmem
    rw [hSfin, hTdef, shiftIterV_targetC] at this
    rw [hTdef]; exact this
  have hnT₄ : neg LAct T ∈ Γ₄ := by rw [hTdef]; exact cT
  -- the leaf and the derivation
  have hleaf : DerivationOf TAct (axL Γ₄ T) Γ₄ := ⟨by simp, Derivation.axL hΓ₄ hT₄ hnT₄⟩
  have hleaf' : DerivationOf TAct (axL Γ₄ T) (ctxVec Γ₀ S).[len S] := by
    show DerivationOf TAct (axL Γ₄ T) (finalCtx Γ₀ S); rw [hSfin]; exact hleaf
  have hdlen_leaf : dlen TAct (axL Γ₄ T) = setLen LAct Γ₄ + 1 :=
    dlen_eq_of_graph hleaf.2 (DlenGraph.axL_iff.mpr rfl)
  have hproof : DerivationOf TAct (chainCode tbl Γ₀ S (axL Γ₄ T)) Γ₀ := chainCode_proof 9 htbl hok hleaf'
  have hcost := dlen_chainCode_le 9 hE1 htbl hok hleaf'
  -- the closing block's cost
  have hgoalLen : formulaLen LAct (goalFact (^&js) (bnum (dlen TAct ρ))) ≤ setLen LAct Γ₃ := by
    have h := formulaLen_le_setLen_of_mem (L := LAct) vgoal
    rwa [formulaLen_neg_eq (isFormula_goalFact (by simp) (isSemiterm_bnum_LAct 0 _))] at h
  set Q := topQ'' B E Ck Cσ 0 (dlen TAct ρ) (setLen LAct Γ₀) (fvOccS LAct Γ₀) (len (rootSteps x)) m with hQdef
  set D := closeD N' B' b (dlen TAct ρ) with hDdef
  -- the pin's shapes at `lk = 0`
  have e01 : (Cσ : V) * (0 + 1) = Cσ := by rw [zero_add, mul_one]
  have hQp : (Cσ : V) ≤ kitQ (Cσ : V) B E :=
    le_mul_of_one_le_right zero_le (one_le_mul_of_one_le_of_one_le le_add_self le_add_self)
  have hDp : (Cσ : V) ≤ kitD (Cσ : V) 0 := le_of_eq (by unfold kitD; simp)
  have hGp : growK B E (Cσ : V) ≤ growK B E (kitQ (Cσ : V) B E) := growK_mono hQp
  have hS2 : setLen LAct Γ₂ ≤ topS2' B E Cσ 0 (setLen LAct Γ₀) (fvOccS LAct Γ₀) (len (rootSteps x)) := by
    unfold topS2' ctxB
    rw [e01]
    refine le_trans pS' (add_le_add (add_le_add rS' (mul_le_mul plen rF' zero_le zero_le)) ?_)
    exact mul_le_mul (add_le_add (mul_le_mul plen plen zero_le zero_le) plen) hGp zero_le zero_le
  have hF2 : fvOccS LAct Γ₂ ≤ topF2' B E Cσ 0 (fvOccS LAct Γ₀) (len (rootSteps x)) := by
    unfold topF2'
    rw [e01]
    exact le_trans pF' (add_le_add rF' (mul_le_mul plen hGp zero_le zero_le))
  have hS3 : setLen LAct Γ₃ ≤ topS3'' B E Ck Cσ 0 (dlen TAct ρ) (setLen LAct Γ₀) (fvOccS LAct Γ₀) (len (rootSteps x)) m :=
    le_trans vS (ctxBoundG_le_ctxB hS2 hF2)
  have hF3 : fvOccS LAct Γ₃ ≤ topF3'' B E Ck Cσ 0 (dlen TAct ρ) (fvOccS LAct Γ₀) (len (rootSteps x)) m :=
    le_trans vF (add_le_add hF2 le_rfl)
  have hBE : B * E ≤ Q := by rw [hQdef, topQ'']; exact le_add_self
  have hQg : 4 * formulaLen LAct (goalFact (^&js) (bnum (dlen TAct ρ))) ≤ Q := by
    rw [hQdef, topQ'']
    exact le_trans (mul_le_mul_of_nonneg_left (le_trans hgoalLen hS3) zero_le) le_self_add
  have hsz : SizeOK Q D (closeStepsC σ b ρ js tN) := by
    unfold closeStepsC
    refine sizeOK_appendV ((sizeOK_goalElim (D := D) (by simp) (isSemiterm_bnum_LAct 0 _)).mono hQg le_rfl) ?_
    have hE1' : (1 : V) ≤ E := hE1
    have hbd : IsSemiterm LAct (0 : V) (bnum (dlen TAct ρ)) := isSemiterm_bnum_LAct 0 _
    refine sizeOK_cons (stepSizeOK_sLemma
      (le_trans (formulaLen_leFact_le hE1' hbd hbb r_d r_b) (le_trans (mul_le_mul_of_nonneg_right hPle zero_le) hBE))
      (le_trans (dlen_leCode_le' htblN hlen) (by rw [hDdef, closeD]))) ?_
    refine sizeOK_cons (stepSizeOK_horn0 (ttag_dlenDefIntro rfl _)) ?_
    refine sizeOK_cons (stepSizeOK_horn0 (ttag_proofIntro rfl _)) ?_
    refine sizeOK_cons (stepSizeOK_horn0 (ttag_leTrans _)) ?_
    refine sizeOK_cons (stepSizeOK_horn0 (ttag_lenDerIntro rfl _)) ?_
    exact sizeOK_single (show StepSizeOK Q D _ from Or.inl (by simp [stepLenDerCong]))
  have ccost := costSum_le_of_sizeOK 8 hE1 htbl hB cok hsz
  rw [clen] at ccost
  obtain ⟨_, cS⟩ := ctxVec_len_le_sizeOK 8 hE1 htbl hB cok hsz (len (closeStepsC σ b ρ js tN)) le_rfl
  have cS' : setLen LAct Γ₄ ≤ setLen LAct Γ₃ + len (closeStepsC σ b ρ js tN) * fvOccS LAct Γ₃ +
      (len (closeStepsC σ b ρ js tN) * len (closeStepsC σ b ρ js tN) + len (closeStepsC σ b ρ js tN)) * growK B E Q := cS
  rw [clen] at cS'
  have h11 : (11 : V) ≤ 15 := by norm_num
  have h132 : (11 * 11 + 11 : V) ≤ 15 * 15 + 15 := by norm_num
  -- the total
  refine ⟨dlen TAct (chainCode tbl Γ₀ S (axL Γ₄ T)), len (rootSteps x), ?_, rlen, ?_⟩
  · refine ⟨chainCode tbl Γ₀ S (axL Γ₄ T), ?_, le_refl (dlen TAct (chainCode tbl Γ₀ S (axL Γ₄ T)))⟩
    rw [boxSentenceCode_eq, ← hTdef]
    have e : insert T (∅ : V) = {T} := mem_ext fun _ ↦ by simp
    show DerivationOf TAct _ {T}
    rw [← e, ← hΓ₀def]; exact hproof
  · have hsplit : costSum N E Γ₀ S = costSum N E Γ₀ (rootSteps x) +
        (costSum N E Γ₁ P + (costSum N E Γ₂ L₁ + costSum N E Γ₃ (closeStepsC σ b ρ js tN))) := by
      rw [hSdef, topListC, ← hxdef, ← hjsdef, costSum_appendV, costSum_appendV, costSum_appendV, ← hΓ₁def, ← hΓ₂def,
        ← hΓ₃def]
    have h_leaf : setLen LAct Γ₄ + 1 ≤ topS3'' B E Ck Cσ 0 (dlen TAct ρ) (setLen LAct Γ₀) (fvOccS LAct Γ₀) (len (rootSteps x)) m +
        15 * topF3'' B E Ck Cσ 0 (dlen TAct ρ) (fvOccS LAct Γ₀) (len (rootSteps x)) m + (15 * 15 + 15) * growK B E Q + 1 :=
      add_le_add (le_trans cS' (add_le_add (add_le_add hS3 (mul_le_mul h11 hF3 zero_le zero_le))
        (mul_le_mul_of_nonneg_right h132 zero_le))) le_rfl
    have h_root : costSum N E Γ₀ (rootSteps x) ≤
        len (rootSteps x) * (stepK N E B + 36 * topS1 B E (setLen LAct Γ₀) (fvOccS LAct Γ₀) (len (rootSteps x))) := by
      unfold topS1; unfold ctxBound at rcost; exact rcost
    have h_pin : costSum N E Γ₁ P ≤ (Cσ : V) * (0 + 1) *
        (costK N E B ((9 : ℕ) : V) (kitQ (Cσ : V) B E) (kitD (Cσ : V) 0) +
          38 * (ctxB (growK B E (kitQ (Cσ : V) B E)) (topS1 B E (setLen LAct Γ₀) (fvOccS LAct Γ₀) (len (rootSteps x)))
            (topF1 B E (fvOccS LAct Γ₀) (len (rootSteps x))) ((Cσ : V) * (0 + 1)) +
            (topF1 B E (fvOccS LAct Γ₀) (len (rootSteps x)) + (Cσ : V) * (0 + 1) * growK B E (kitQ (Cσ : V) B E)))) := by
      rw [e01]
      refine le_trans pcost (mul_le_mul_of_nonneg_left (add_le_add (costK_mono hQp hDp) (mul_le_mul_of_nonneg_left
        (add_le_add (le_trans (ctxBoundG_mono2 hGp le_rfl) (ctxBoundG_le_ctxB rS' rF'))
          (add_le_add rF' (mul_le_mul_of_nonneg_left hGp zero_le))) zero_le)) zero_le)
    have h_ver : costSum N E Γ₂ L₁ ≤ (Ck : V) * (dlen TAct ρ + 1) ^ m *
        (costK N E B ((9 : ℕ) : V) (kitQ (Ck : V) B E) (kitD (Ck : V) (dlen TAct ρ)) +
          38 * (ctxB (growK B E (kitQ (Ck : V) B E)) (topS2' B E Cσ 0 (setLen LAct Γ₀) (fvOccS LAct Γ₀) (len (rootSteps x)))
            (topF2' B E Cσ 0 (fvOccS LAct Γ₀) (len (rootSteps x))) ((Ck : V) * (dlen TAct ρ + 1) ^ m) +
            (topF2' B E Cσ 0 (fvOccS LAct Γ₀) (len (rootSteps x)) + (Ck : V) * (dlen TAct ρ + 1) ^ m * growK B E (kitQ (Ck : V) B E)))) :=
      le_trans vcost (mul_le_mul_of_nonneg_left (add_le_add le_rfl (mul_le_mul_of_nonneg_left
        (add_le_add (ctxBoundG_le_ctxB hS2 hF2) (add_le_add hF2 le_rfl)) zero_le)) zero_le)
    have h_close : costSum N E Γ₃ (closeStepsC σ b ρ js tN) ≤
        15 * (costK N E B ((8 : ℕ) : V) Q D + (3 * ((8 : ℕ) : V) + 11) *
          ((topS3'' B E Ck Cσ 0 (dlen TAct ρ) (setLen LAct Γ₀) (fvOccS LAct Γ₀) (len (rootSteps x)) m +
            15 * topF3'' B E Ck Cσ 0 (dlen TAct ρ) (fvOccS LAct Γ₀) (len (rootSteps x)) m + (15 * 15 + 15) * growK B E Q) +
           (topF3'' B E Ck Cσ 0 (dlen TAct ρ) (fvOccS LAct Γ₀) (len (rootSteps x)) m + 15 * growK B E Q))) := by
      refine le_trans ccost (mul_le_mul h11 (add_le_add le_rfl (mul_le_mul_of_nonneg_left
        (add_le_add ?_ (add_le_add hF3 (mul_le_mul h11 le_rfl zero_le zero_le))) zero_le)) zero_le zero_le)
      unfold ctxBoundG
      exact add_le_add (add_le_add hS3 (mul_le_mul h11 hF3 zero_le zero_le)) (mul_le_mul_of_nonneg_right h132 zero_le)
    refine le_trans hcost ?_
    rw [hdlen_leaf, hsplit]
    unfold topBound''
    calc setLen LAct Γ₄ + 1 + (costSum N E Γ₀ (rootSteps x) + (costSum N E Γ₁ P +
          (costSum N E Γ₂ L₁ + costSum N E Γ₃ (closeStepsC σ b ρ js tN))))
        = (setLen LAct Γ₄ + 1) + costSum N E Γ₀ (rootSteps x) + costSum N E Γ₁ P + costSum N E Γ₂ L₁ +
          costSum N E Γ₃ (closeStepsC σ b ρ js tN) := by ring
      _ ≤ _ := add_le_add (add_le_add (add_le_add (add_le_add h_leaf h_root) h_pin) h_ver) h_close

end topC

/-! ## 6. The package and the polynomial bound -/

section packageC

/-- **The closed kit package**: the closed table (with the row-body bound `B` covering `Ple`), the numeral
table, the graph's existence half, the kit at `m`, and the `numId` pin for every sentence with its constant
`Cσ σ`. -/
def KitPackageC (N B N' B' Ck Cv : ℕ) (Cσ : Sentence LAct → ℕ) (m : ℕ) : Prop :=
  ∀ (V : Type) [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁],
    ∃ tbl Wl Wc W₁ W₂ W T : V, TableOK tbl N ∧ ClosedTable tbl ∧
      (∀ j < len tbl, formulaLen LAct (rowB tbl.[j]) ≤ B) ∧ formulaLen LAct (Ple : V) ≤ B ∧
      NumTableOK T N' B' ∧
      (∀ ρ E : V, Derivation TAct ρ → (Cv : V) * p3 (dlen TAct ρ + 1) + 6 * dlen TAct ρ + 1 ≤ E →
        ∃ A L : V, AxmTableOK' tbl E walkPieces A Cv ∧ VerifyGraph'' walkPieces Wl Wc W₁ W₂ W T A ρ L) ∧
      VerifyKit''' tbl N B Wl Wc W₁ W₂ W T Cv Ck m ∧
      ∀ σ : Sentence LAct, ∀ {Γ i E : V}, IsFormulaSet LAct Γ → DossF walkPieces Γ 0 (⌜σ⌝ : V) i →
        ((Cσ σ : ℕ) : V) + i ≤ E → ∃ P : V, NumInv tbl E Γ (Cσ σ) P (eqFact (^&i) (numeral (⌜σ⌝ : V)))

/-- **The closed package holds at `m = 4`** (`Package.kitPackage'''_of_size'` on the closed table, with
`sizeThmAll_holds` and the `numId` pins in place of `pinKit'_of`). -/
theorem kitPackageC_of : ∃ (N B N' B' Ck Cv : ℕ) (Cσ : Sentence LAct → ℕ), KitPackageC N B N' B' Ck Cv Cσ 4 := by
  obtain ⟨N, B₀, hTab⟩ := exists_closedTableB
  obtain ⟨N', B', hNum⟩ := exists_numTable
  obtain ⟨C, hex⟩ := verifyGraph''_exists_unconditional
  obtain ⟨Cz, hCz⟩ := sizeThmAll_holds N N' B' C
  obtain ⟨Ck, hkit⟩ := verifyKit'''_of N' B' Cz C
  refine ⟨N, B₀ + cPle, N', B', Ck, C, fun σ ↦ Classical.choose (numId_sentence (n := 0) σ), fun V _ _ ↦ ?_⟩
  obtain ⟨tbl, htbl, hC, hB₀⟩ := hTab V
  obtain ⟨tblN, hN⟩ := hNum V
  have hB : ∀ j < len tbl, formulaLen LAct (rowB tbl.[j]) ≤ ((B₀ + cPle : ℕ) : V) := fun j hj ↦
    le_trans (hB₀ j hj) (by exact_mod_cast (by omega : B₀ ≤ B₀ + cPle))
  have hPle : formulaLen LAct (Ple : V) ≤ ((B₀ + cPle : ℕ) : V) := by
    rw [formulaLen_Ple_eq]; exact_mod_cast (by omega : cPle ≤ B₀ + cPle)
  refine ⟨tbl, layoutPieces, certPieces, frag1Pieces, frag2Pieces, proPieces, tblN, htbl, hC, hB, hPle, hN, ?_, ?_, ?_⟩
  · intro ρ E hd hE
    exact hex V htbl hC.indRecTable rfl rfl rfl hd hE
  · exact hkit V htbl hC.proTable hB hPle hN rfl rfl rfl rfl rfl
      (verifySizeOracle_of_sizeThm hCz htbl hC.indRecTable hB hPle hN)
  · intro σ Γ i E hΓ hD hE
    exact Classical.choose_spec (numId_sentence (n := 0) σ) V htbl hC.indRecTable.layoutTable hΓ hD hE

/-- The two scales at `G = b + 1`, `u = 1`: every `u`-graded quantity of the closed top is a constant. -/
lemma pbCtx_closed (b : V) : PBCtx (b + 1) (1 : V) where
  hG := le_add_self
  hu := le_rfl
  huG := le_add_self
  hu3 := by rw [one_pow]; exact le_trans le_add_self (le_mul_of_one_le_left zero_le (by norm_num))

/-- **`closeD` is cubic** in `G = b + 1`. -/
lemma closeD_pb {G : V} (hc : PBCtx G (1 : V)) (N' B' : ℕ) {b d : V} (hb : PB G 1 1 b 1 0) (hd : PB G 1 1 d 1 0) :
    PB G 1 ((1 + 1) * (1 + 2) * (N' + 800 * (B' * (12 * 1 + 3))) + (N' + 800 * (B' * (12 * 1 + 3))))
      (closeD (N' : V) (B' : V) b d) 3 0 := by
  unfold closeD
  have hlb : PB G 1 1 ‖b‖ 1 0 := hb.of_le (length_le b)
  have hld : PB G 1 1 ‖d‖ 1 0 := hd.of_le (length_le d)
  have h12 := twelveLen_pb hc hlb
  have hnc := nodeCost_pb hc (PB.const N') (PB.const B') h12
  have hd1 : PB G 1 (1 + 1) (‖d‖ + 1) 1 0 := hld.add (PB.one'.mono hc (Nat.zero_le _) (Nat.zero_le _))
  have hb2 : PB G 1 (1 + 2) (‖b‖ + 2) 1 0 := hlb.add (PB.two.mono hc (Nat.zero_le _) (Nat.zero_le _))
  exact ((hd1.mul hb2).mul hnc).add (hnc.mono hc (by norm_num) le_rfl)

/-- **Closed inner necessitation at degree `deg m` from the closed package**
(`Assemble.boundedInnerNec_of_kit'''` at `G = b + 1`, `u = 1`). -/
theorem closedInnerNec_of_kit (m : ℕ) (hm3 : 3 ≤ m) {N B N' B' Ck Cv : ℕ} {Cσ : Sentence LAct → ℕ}
    (hpkg : KitPackageC N B N' B' Ck Cv Cσ m) :
    ∀ σ : Sentence LAct, ∃ C : ℕ, ∀ (V : Type) [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁] (b : V),
      LenDerivable TAct b (⌜σ⌝ : V) →
        ∃ e : V, e ≤ (C : V) * (b ^ (deg m) + 1) ∧ LenDerivable TAct e (boxSentenceCode σ b) := by
  intro σ
  obtain ⟨n, hn_def⟩ : ∃ n : ℕ, n = max m 1 := ⟨_, rfl⟩
  have hn : 1 ≤ n := hn_def ▸ le_max_right m 1
  have hmn : m ≤ n := hn_def ▸ le_max_left m 1
  exact ⟨_, fun V _ _ b hb ↦ by
    obtain ⟨tbl, Wl, Wc, W₁, W₂, W, T, htbl, hC, hB, hPle, htblN, hex, hkit, hpin⟩ := hpkg V
    obtain ⟨ρ, hρ, hlen⟩ := hb
    obtain ⟨A, L, hA, hL⟩ := hex ρ (EtopCv σ b (dlen TAct ρ) Ck (Cσ σ) Cv m) hρ.2
      (le_EtopCv_axm σ b (dlen TAct ρ) Ck (Cσ σ) Cv m)
    obtain ⟨e, Lr, he, hLr, hbound⟩ := top_mainC σ m htbl hC hB hPle htblN hkit (hpin σ) hρ hlen hL hA
      (le_EtopCv_top σ b (dlen TAct ρ) Ck (Cσ σ) Cv m)
    refine ⟨e, ?_, he⟩
    have hc := pbCtx_closed b
    -- the graded inputs (`G = b + 1`, `u = 1`)
    have hone : PB (b + 1) (1 : V) 1 (1 : V) 0 0 := PB.one'
    have hb1 : PB (b + 1) (1 : V) 1 b 1 0 := (PB.G_ hc).of_le le_self_add
    have hlb : PB (b + 1) (1 : V) 1 ‖b‖ 1 0 := hb1.of_le (length_le b)
    have hd1 : PB (b + 1) (1 : V) 1 (dlen TAct ρ + 1) 1 0 := (PB.G_ hc).of_le (add_le_add hlen le_rfl)
    have hd0 : PB (b + 1) (1 : V) 1 (dlen TAct ρ) 1 0 := hb1.of_le hlen
    have hld : PB (b + 1) (1 : V) 1 ‖dlen TAct ρ‖ 1 0 := hd0.of_le (length_le _)
    have hCk : PB (b + 1) (1 : V) Ck (Ck : V) 0 0 := PB.const Ck
    have hCσ : PB (b + 1) (1 : V) (Cσ σ) (Cσ σ : V) 0 0 := PB.const _
    have hCv : PB (b + 1) (1 : V) Cv (Cv : V) 0 0 := PB.const Cv
    have hqN : PB (b + 1) (1 : V) (2 * (⌜σ⌝ : ℕ) + 1) (termLen LAct (qNumS σ : V)) 0 0 :=
      PB.natCast _ (termLen_qNumS_le σ)
    have hx : PB (b + 1) (1 : V) (flen (Rewriting.emb σ : Semiproposition LAct 0)) (formulaLen LAct (⌜σ⌝ : V)) 0 0 :=
      PB.natCast _ (le_of_eq (formulaLen_quote_semisentence_V' σ))
    have hdm : PB (b + 1) (1 : V) (1 ^ m) ((dlen TAct ρ + 1) ^ m) n 0 :=
      (hd1.pow m).mono hc (e' := n) (f' := 0) (by omega) (by omega)
    -- `E = EtopCv`: each summand is `≲ G^n`
    have e1 := ((PB.two.mul hx).add (PB.natCast (q := (8 : V)) 8 (by norm_num))).mono hc (e' := n) (f' := 0) (by omega) le_rfl
    have e2 := (hCσ.add (PB.natCast (q := ((0 : V) + 2)) 2 (by norm_num))).mono hc (e' := n) (f' := 0) (by omega) le_rfl
    have e3 := (hCk.mul (hdm.add ((PB.natCast (q := ((0 : V) + 0)) 0 (by norm_num)).mono hc (e' := n) (f' := 0) (by omega) le_rfl))).mono hc (e' := n) (f' := 0) (by omega) le_rfl
    have e4 := (((PB.natCast (q := ((0 : V) + 0 + 1)) 1 (by norm_num)).mono hc (e' := n) (f' := 0) (by omega) le_rfl).add
      ((hCk.mul hdm).mono hc (e' := n) (f' := 0) (by omega) le_rfl)).add
      ((PB.natCast (q := (4 : V)) 4 (by norm_num)).mono hc (e' := n) (f' := 0) (by omega) le_rfl)
    have e5 := hqN.mono hc (e' := n) (f' := 0) (by omega) le_rfl
    have e6 := (PB.of_le (termLen_bnum_le_V b) ((hlb.smul 6).add (hone.mono hc (e' := 1) (f' := 0) (by omega) le_rfl))).mono hc
      (e' := n) (f' := 0) (by omega) le_rfl
    have e7 := (PB.of_le (termLen_bnum_le_V (dlen TAct ρ)) ((hld.smul 6).add (hone.mono hc (e' := 1) (f' := 0) (by omega) le_rfl))).mono hc
      (e' := n) (f' := 0) (by omega) le_rfl
    have e8a := (hCv.mul ((hd1.mul hd1).mul hd1)).mono hc (e' := n) (f' := 0) (by omega) le_rfl
    have e8b := ((hd0.smul 6).add (hone.mono hc (e' := 1) (f' := 0) (by omega) le_rfl)).mono hc (e' := n) (f' := 0) (by omega) le_rfl
    have e8 := e8a.add e8b
    have hE₀ := ((((((e1.add e2).add e3).add e4).add e5).add e6).add e7).add e8
    have hE := PB.of_le (q := EtopCv σ b (dlen TAct ρ) Ck (Cσ σ) Cv m) (le_of_eq (by
      unfold EtopCv EtopC eWalkC ePinC eVerC eJsC eQC eK eD p3; push_cast; ring)) hE₀
    -- `S₀, F₀ ≤ |PlenDer| · (|bnum b| + |numeral ⌜σ⌝|)`, linear in `G`
    have hq : IsSemiterm LAct (0 : V) (qNumS σ) := isSemiterm_qNumS σ
    have hbb : IsSemiterm LAct (0 : V) (bnum b) := isSemiterm_bnum_LAct 0 b
    have hTf : IsFormula LAct (lenDerFact (bnum b) (qNumS σ)) := isFormula_lenDerFact hbb hq
    have hB' : formulaLen LAct (lenDerFact (bnum b) (qNumS σ)) ≤
        formulaLen LAct (PlenDer : V) * ((6 * ‖b‖ + 1) + ((2 * (⌜σ⌝ : ℕ) + 1 : ℕ) : V)) :=
      formulaLen_lenDerFact_le (le_trans le_add_self le_self_add) hbb hq
        (le_trans (termLen_bnum_le_V b) le_self_add) (le_trans (termLen_qNumS_le σ) le_add_self)
    have hBp := ((hlb.smul 6).add (hone.mono hc (e' := 1) (f' := 0) (by omega) le_rfl)).add
      ((PB.const (2 * (⌜σ⌝ : ℕ) + 1)).mono hc (e' := 1) (f' := 0) (by omega) le_rfl)
    have hPb := PB.natCast (G := b + 1) (u := (1 : V))
      (flen (Rewriting.emb (Semiformula.lMap emb (↑(lenDerivableDef TAct) : ArithmeticSemisentence 2)) : Semiproposition LAct 2))
      (le_of_eq (formulaLen_quote_semisentence_V' _))
    have hTlen := PB.of_le hB' (hPb.mul hBp)
    have hS := PB.of_le (le_trans (setLen_insert_le (L := LAct) (lenDerFact (bnum b) (qNumS σ)) (∅ : V))
      (by rw [setLen_empty', zero_add])) hTlen
    have hF := PB.of_le (le_trans (fvOccS_insert_le (L := LAct) (lenDerFact (bnum b) (qNumS σ)) (∅ : V))
      (by rw [fvOccS_empty, zero_add]; exact fvOccF_le_formulaLen hTf.isUFormula)) hTlen
    -- `Lr ≤ 12|⌜σ⌝| + 9`, a constant
    have h1 : Lr ≤ 12 * formulaLen LAct (⌜σ⌝ : V) + 9 := by
      have : Lr + 4 ≤ 12 * formulaLen LAct (⌜σ⌝ : V) + 9 + 4 := by
        refine le_trans hLr (le_of_eq ?_); ring
      exact le_of_add_le_add_right this
    have hL := (PB.of_le h1 (((PB.natCast (q := (12 : V)) 12 (by norm_num)).mul hx).add
      (PB.natCast (q := (9 : V)) 9 (by norm_num)))).mono hc (e' := 0) (f' := 1) le_rfl (by norm_num)
    -- `lk + 1 = 0 + 1 ≤ u`
    have hu1 : PB (b + 1) (1 : V) 1 ((0 : V) + 1) 0 1 := PB.of_le (by simp) (PB.u_ hc)
    have hD := closeD_pb hc N' B' hb1 hd0
    have hmain := topBound''_pb hc m n hmn hn (PB.const N) (PB.const B) hE hCk hCσ hu1 hd1 hdm hS hF hL hD
    have hfin := PB.final_pow hc hmain
    rw [show deg m = 4 * n by rw [deg, hn_def]]
    exact le_trans hbound hfin⟩

end packageC

/-! ## 7. THE THEOREM: closed inner necessitation at degree 16 -/

/-- **U10 in closed-sentence, arbitrary-budget form**: for every `LAct`-sentence `σ` there is a standard
constant `C` such that, in every model `V` and at every budget `b : V`, a `TAct`-proof of `⌜σ⌝` of length
`≤ b` yields a `TAct`-proof of the closed box code `boxSentenceCode σ b` — the sentence "`σ` has a proof of
length `≤ b`", the budget written as the binary numeral `bnum b` — of length `≤ C·(b^16 + 1)`. -/
theorem closedInnerNec_sixteen : ∀ σ : Sentence LAct, ∃ C : ℕ,
    ∀ (V : Type) [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁] (b : V),
      LenDerivable TAct b (⌜σ⌝ : V) →
        ∃ e : V, e ≤ (C : V) * (b ^ 16 + 1) ∧ LenDerivable TAct e (boxSentenceCode σ b) := by
  obtain ⟨N, B, N', B', Ck, Cv, Cσ, hpkg⟩ := kitPackageC_of
  exact closedInnerNec_of_kit 4 (by norm_num) hpkg

/-- The same with the box code written out as the fact `lenDerFact (bnum b) (numeral ⌜σ⌝)`. -/
theorem closedInnerNec_sixteen' : ∀ σ : Sentence LAct, ∃ C : ℕ,
    ∀ (V : Type) [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁] (b : V),
      LenDerivable TAct b (⌜σ⌝ : V) →
        ∃ e : V, e ≤ (C : V) * (b ^ 16 + 1) ∧ LenDerivable TAct e (lenDerFact (bnum b) (numeral (⌜σ⌝ : V))) := by
  intro σ
  obtain ⟨C, hC⟩ := closedInnerNec_sixteen σ
  refine ⟨C, fun V _ _ b hb ↦ ?_⟩
  obtain ⟨e, he, hd⟩ := hC V b hb
  exact ⟨e, he, by rwa [boxSentenceCode_eq] at hd⟩

end ArithS
