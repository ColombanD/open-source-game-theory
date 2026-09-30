import ArithS.Cells.DIMCID
import PrisonersDilemma.Bots.LlmGenerations.CIMCIC

/-!
# ArithS.Cells.CIMCIC — CIMCIC × Dupoc, CIMCIC × Mirror and CIMCIC × CIMCIC, all `(C, C)`, in PA-`S'`

`Research/Notes/ROUTE_B_SCOPE.md` §3 Phase 2: the CIMCIC family — the arithmetized
twins of the engine's `llm_outcome_CIMCIC_vs_DupocBot = (C, C)` (`mutual_pblt_engine_id`),
`llm_outcome_CIMCIC_vs_MirrorBot = (C, C)` (`Pf.simStep`) and `llm_outcome_CIMCIC_vs_CIMCIC = (C, C)`
(`Pf.implRefl`). The engine's bot is
`CIMCIC k := .search k (.impl (.plays .self .opp C) (.plays .opp .self C)) (.const C) (.const D)`
("if I can prove that my cooperating implies your cooperating, cooperate; else defect"). The file is
`Cells/DIMCID.lean` re-run on the guard `phiC := .impl (.plays .self .opp C) (.plays .opp .self C)` with
the branches exchanged (found ⇒ `C` = `pConst 0`): the same canonical description (§2), the truth of the
template at a frame (§3, from DIMCID's `eval_template_plays_self_opp_V`/`_opp_self_V`), the fixed formulas
generic in the opponent triple (§4, `qCG X U W`/`qCTG`), the instance equations on codes (§5), the
search clauses (found ⇒ `C` for `CimcicV`, found ⇒ `D` for the transposed searcher `CimcicTV`), and the
conjunction family `pGC X U W := qCG X U W ⋏ qCTG (swap X) (swap U) (swap W)` (§6). The cells:
* **Cell 1 (§7), the MUTUAL family CIMCIC × Dupoc `(C, C)`** (the engine's `mutual_pblt_engine_id`):
  `(TD, uD, wD)` describes `DupocV k` and its transposition describes `CupodV k`. CIMCIC's guard against
  Dupoc says "I play C against Dupoc ⇒ Dupoc plays C against me", and Dupoc's guard against CIMCIC
  (`qDCi := qG 0 TD uD wD TCi uCi wCi`, DIMCID's generic hand-written instance) says "CIMCIC plays C
  against me" — each searcher's box is what the other's guard needs, so the family is the four-guard
  conjunction `pCiD := pGC TD uD wD ⋏ (qDCi ⋏ τqDCi)`. A box of `pCiD(k)` yields the four guard boxes
  by DIMCID's two-level ∧-elimination (`pCiD_all_V`, slack `(14, 16)`): CIMCIC cooperates with Dupoc,
  Dupoc cooperates with CIMCIC, the transposed searcher defects against Cupod and Cupod defects against
  it — so CIMCIC's implications have TRUE consequents and Dupoc's/Cupod's atoms are TRUE, in both
  readings (`loebSound_pCiD : LoebSound pCiD 14 16`); `family_found` then gives
  **`loeb_Cimcic_vs_Dupoc`** (both cooperate at fuel 2) and
  `loeb_Cimcic_vs_Dupoc_guards` (both boxes). The swap reading is τ(CIMCIC) × Cupod, not a
  zoo cell, and is handled by the transposed code exactly as DIMCID's.
* **Cell 2 (§8), CIMCIC × Mirror `(C, C)`**: Mirror's closed triple; a box of `pCMi := pGC (cl TM) (numT 0)
  (numT 1)` makes `CimcicV k` cooperate (fuel 2), Mirror COPIES (fuel 3, `mirror_copies2_V`), so the
  implication's consequent holds; **`loeb_Cimcic_vs_Mirror`**.
* **Cell 3 (§9), CIMCIC × CIMCIC `(C, C)` — NO Löb**: the guard at the frame `(CimcicV k, CimcicV k)` is
  `qCC := qCG TCi uCi wCi`, whose two atoms coincide ("`CimcicV k` plays C against `CimcicV k`" twice), so
  `qCC(k)` is a tautology in both readings and `TAct ⊢ ∀¹ qCC` by completeness (`tact_proves_qCC`) —
  the `S'` twin of the engine's `implRefl`. Then the `exists_forward_length`/`forward_inst_V` pattern:
  a proof code of `∀¹ qCC` of some standard length `N` in every model (`exists_qCC_length`), instantiated
  at `binNumeral k` (`qCC_inst_V`, length `N + 5|qCC(k)| + 3|qCC| + |binNumeral k| + 7`); at ℕ the instance costs
  `K₀ + K₁·size k` (`lenBoxNat_inst_size` + `formulaLenMeta_subst_binNumeralMeta_le`), below `k` for all large `k`
  (`poly_size_le_eventually`): **`pos_Cimcic_vs_Cimcic_guard`** and **`pos_Cimcic_vs_Cimcic`** — with NO
  `BoundedInnerNec` hypothesis at all.

Conventions (`HANDOVER_ARITHMETIZED_S.md` §5–6): every threshold and constant is EXISTENTIAL; `simp`
never sees a closed quote of `templateC`/`qCC`/`pCiD` (the quote equations are for VARIABLE sentences,
instantiated; `rfl`-bridges); `omega` is never asked about `V`; at `V = ℕ` the thresholds are STRICT
(`k₀ < k`) and the V-generic `≤` is bridged by `le_def` (`Cell.cell_core`'s idiom).
-/

namespace ArithS

open FFL FFL.FirstOrder Arithmetic Bootstrapping
open PeanoMinus ISigma0 ISigma1
open FFL.FirstOrder.Arithmetic.Bootstrapping.Arithmetic
open LAct

variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

/-! ### 0. The guard template -/

section template

/-- CIMCIC's guard: "my cooperating implies your cooperating". -/
def phiC : PD.Formula := .impl (.plays .self .opp .C) (.plays .opp .self .C)

lemma phiC_transpose : phiC.transpose = .impl (.plays .self .opp .D) (.plays .opp .self .D) := rfl

lemma fragF_phiC : fragF phiC = true := rfl

/-- The six-variable template of CIMCIC's guard (a CLOSED constant, never evaluated). -/
noncomputable def templateC : Semisentence LAct 6 := template phiC

/-- The template of the transposed guard. -/
noncomputable def templateCT : Semisentence LAct 6 := template phiC.transpose

lemma templateC_eq : templateC = template (.plays .self .opp .C) 🡒 template (.plays .opp .self .C) := template_impl _ _

lemma templateCT_eq : templateCT = template (.plays .self .opp .D) 🡒 template (.plays .opp .self .D) := template_impl _ _

lemma lMap_swap_templateC : Semiformula.lMap swap templateC = templateCT := lMap_swap_template phiC fragF_phiC

lemma lMap_swap_templateCT : Semiformula.lMap swap templateCT = templateC := by
  rw [← lMap_swap_templateC, lMap_swap_swap]

end template

/-! ### 1. CIMCIC in every model, and its transposition -/

section cimcic

/-- `CIMCIC k` in an arbitrary model: search the guard within budget `k`; found ⇒ `C` (`pConst 0`),
else `D` (`pConst 1`). -/
noncomputable def CimcicV (k : V) : V := pSearch k (⌜templateC⌝ : V) (pConst 0) (pConst 1)

/-- The transposed searcher (τ(CIMCIC)): its guard is the transposed template, found ⇒ `D`. -/
noncomputable def CimcicTV (k : V) : V := pSearch k (⌜templateCT⌝ : V) (pConst 1) (pConst 0)

/-- `CimcicV` IS the generic engine searcher `SV templateC 0` of `Cells/Common/Bots` (up to the casts of the
branch constants). -/
lemma CimcicV_eq_SV (k : V) : CimcicV k = SV templateC 0 k := by
  unfold CimcicV SV; norm_num

lemma CimcicTV_eq_SV (k : V) : CimcicTV k = SV templateCT 1 k := by
  unfold CimcicTV SV; norm_num

/-- `CIMCIC k` at `ℕ`. -/
noncomputable def Cimcic (k : ℕ) : ℕ := CimcicV (V := ℕ) k

lemma CimcicV_nat (k : ℕ) : CimcicV (V := ℕ) k = Cimcic k := rfl

/-- **The bridge to the engine**: the code of the engine's `CIMCIC k` is `Cimcic k`. -/
theorem progCode_CIMCIC (k : ℕ) : progCode (PD.Bots.CIMCIC k) = Cimcic k := by
  simp [PD.Bots.CIMCIC, actCode]
  change pSearch k (templateCode phiC) _ _ = _
  rw [templateCode_eq_quote_template phiC (noSelfIdxF_of_fragF _ fragF_phiC)]; rfl

theorem transposeCode_CimcicV (k : V) : transposeCode (CimcicV k) = CimcicTV k := by
  unfold CimcicV CimcicTV transposeCode
  rw [revalue_search, revalue_const, revalue_const, revalueTemplate_quote_sentence₆_V, lMap_swap_templateC]
  simp [revalueAction]

theorem transposeCode_CimcicTV (k : V) : transposeCode (CimcicTV k) = CimcicV k := by
  rw [← transposeCode_CimcicV, transposeCode_transposeCode]

end cimcic

/-! ### 2. The canonical description of `CimcicV k` is `k`-independent apart from the budget -/

section canonical

/-- The budget-independent inner part of CIMCIC's code. -/
noncomputable def innerCi : ℕ := ppair (⌜templateC⌝ : ℕ) (ppair (pConst 0) (pConst 1))

/-- The budget-independent inner part of the transposed searcher's code. -/
noncomputable def innerCT : ℕ := ppair (⌜templateCT⌝ : ℕ) (ppair (pConst 1) (pConst 0))

lemma innerCi_def : innerCi = ppair (⌜templateC⌝ : ℕ) (ppair (pConst 0) (pConst 1)) := rfl
lemma innerCT_def : innerCT = ppair (⌜templateCT⌝ : ℕ) (ppair (pConst 1) (pConst 0)) := rfl

/- Closed constants built from the giant templates: never to be evaluated. -/
attribute [irreducible] innerCi innerCT

lemma cast_innerCi : ((innerCi : ℕ) : V) = ppair (⌜templateC⌝ : V) (ppair (pConst 0) (pConst 1)) := by
  rw [innerCi_def, cast_ppair, cast_ppair, cast_pConst, cast_pConst, coe_quote_sentence₆]
  push_cast
  rfl

lemma cast_innerCT : ((innerCT : ℕ) : V) = ppair (⌜templateCT⌝ : V) (ppair (pConst 1) (pConst 0)) := by
  rw [innerCT_def, cast_ppair, cast_ppair, cast_pConst, cast_pConst, coe_quote_sentence₆]
  push_cast
  rfl

lemma CimcicV_eq_inner (k : V) : CimcicV k = ppair 6 (ppair k (innerCi : V)) + 1 := by
  rw [cast_innerCi]; rfl
lemma CimcicTV_eq_inner (k : V) : CimcicTV k = ppair 6 (ppair k (innerCT : V)) + 1 := by
  rw [cast_innerCT]; rfl

lemma CimcicV_lt_CimcicTV_iff (k : V) : CimcicV k < CimcicTV k ↔ innerCi < innerCT := by
  rw [CimcicV_eq_inner, CimcicTV_eq_inner, pSearchInner_lt_iff, Nat.cast_lt]

lemma CimcicTV_lt_CimcicV_iff (k : V) : CimcicTV k < CimcicV k ↔ innerCT < innerCi := by
  rw [CimcicV_eq_inner, CimcicTV_eq_inner, pSearchInner_lt_iff, Nat.cast_lt]

/-- The stored template of the canonical searcher (`⌜templateC⌝` or `⌜templateCT⌝`). -/
noncomputable def gCi : ℕ := if innerCi ≤ innerCT then (⌜templateC⌝ : ℕ) else (⌜templateCT⌝ : ℕ)
/-- Its then-branch. -/
noncomputable def pCi : ℕ := if innerCi ≤ innerCT then pConst 0 else pConst 1
/-- Its else-branch. -/
noncomputable def qCi : ℕ := if innerCi ≤ innerCT then pConst 1 else pConst 0
/-- The first re-valuation term of the description of `CimcicV k`. -/
noncomputable def uCi : ClosedSemiterm LAct 0 :=
  if innerCi < innerCT then cterm Act.C else if innerCT < innerCi then cterm Act.D else numT 0
/-- The second re-valuation term of the description of `CimcicV k`. -/
noncomputable def wCi : ClosedSemiterm LAct 0 :=
  if innerCi < innerCT then cterm Act.D else if innerCT < innerCi then cterm Act.C else numT 1

lemma CimcicV_eq_cast (k : V) :
    CimcicV k = pSearch k ((⌜templateC⌝ : ℕ) : V) ((pConst 0 : ℕ) : V) ((pConst 1 : ℕ) : V) := by
  unfold CimcicV; rw [coe_quote_sentence₆, cast_pConst, cast_pConst]; push_cast; rfl

lemma CimcicTV_eq_cast (k : V) :
    CimcicTV k = pSearch k ((⌜templateCT⌝ : ℕ) : V) ((pConst 1 : ℕ) : V) ((pConst 0 : ℕ) : V) := by
  unfold CimcicTV; rw [coe_quote_sentence₆, cast_pConst, cast_pConst]; push_cast; rfl

/-- **The canonical code of `CimcicV k` is a searcher with the (cast) `k`-independent inner triple.** -/
theorem canonical_CimcicV (k : V) : canonical (CimcicV k) = pSearch k (gCi : V) (pCi : V) (qCi : V) := by
  by_cases h : innerCi ≤ innerCT
  · simp only [gCi, pCi, qCi, if_pos h]
    rcases Nat.lt_or_eq_of_le h with h' | h'
    · rw [canonical_of_lt (by rw [transposeCode_CimcicV]; exact (CimcicV_lt_CimcicTV_iff k).mpr h')]
      exact CimcicV_eq_cast k
    · rw [canonical_of_eq (by rw [transposeCode_CimcicV, CimcicV_eq_inner, CimcicTV_eq_inner, h'])]
      exact CimcicV_eq_cast k
  · simp only [gCi, pCi, qCi, if_neg h]
    rw [canonical_of_gt (by rw [transposeCode_CimcicV]; exact (CimcicTV_lt_CimcicV_iff k).mpr (Nat.lt_of_not_le h)),
      transposeCode_CimcicV]
    exact CimcicTV_eq_cast k

theorem revalueU_CimcicV (k : V) : revalueU (CimcicV k) = (⌜uCi⌝ : V) := by
  unfold revalueU uCi
  rw [transposeCode_CimcicV]
  by_cases h1 : innerCi < innerCT
  · rw [if_pos ((CimcicV_lt_CimcicTV_iff k).mpr h1), if_pos h1, quote_cterm_C]
  · rw [if_neg (fun h ↦ h1 ((CimcicV_lt_CimcicTV_iff k).mp h)), if_neg h1]
    by_cases h2 : innerCT < innerCi
    · rw [if_pos ((CimcicTV_lt_CimcicV_iff k).mpr h2), if_pos h2, quote_cterm_D]
    · rw [if_neg (fun h ↦ h2 ((CimcicTV_lt_CimcicV_iff k).mp h)), if_neg h2, quote_numT]
      simp

theorem revalueW_CimcicV (k : V) : revalueW (CimcicV k) = (⌜wCi⌝ : V) := by
  unfold revalueW wCi
  rw [transposeCode_CimcicV]
  by_cases h1 : innerCi < innerCT
  · rw [if_pos ((CimcicV_lt_CimcicTV_iff k).mpr h1), if_pos h1, quote_cterm_D]
  · rw [if_neg (fun h ↦ h1 ((CimcicV_lt_CimcicTV_iff k).mp h)), if_neg h1]
    by_cases h2 : innerCT < innerCi
    · rw [if_pos ((CimcicTV_lt_CimcicV_iff k).mpr h2), if_pos h2, quote_cterm_C]
    · rw [if_neg (fun h ↦ h2 ((CimcicTV_lt_CimcicV_iff k).mp h)), if_neg h2, quote_numT]
      simp

/-- The one-variable description term of CIMCIC, over `LAct`. -/
noncomputable def TCi : Semiterm LAct Empty 1 := Semiterm.lMap emb (searchT1 gCi pCi qCi)

lemma lMap_swap_TCi : Semiterm.lMap swap TCi = TCi := term_lMap_swap_emb _

/-- The code of `TCi` (over `LAct`) is the `ℒₒᵣ` tower. -/
theorem quote_emb_TCi :
    (⌜(Rew.emb TCi : SyntacticSemiterm LAct 1)⌝ : V) =
    ppairTerm (binNumeral 6) (ppairTerm (^#0) (ppairTerm (binNumeral (gCi : V)) (ppairTerm (codeTerm (pCi : V)) (codeTerm (qCi : V))))) ^+ 𝟏 := by
  unfold TCi
  rw [term_emb_lMap_emb_n, quote_term_lMap_emb, quote_emb_searchT1]

/-- **`TCi` at the budget `k` denotes the canonical code of `CimcicV k`** (in `stdReadingV V`). -/
theorem val_TCi_V (k : V) : TCi.val (s := stdReadingV V) ![k] Empty.elim = canonical (CimcicV k) := by
  unfold TCi
  rw [Semiterm.val_lMap, stdReadingV_lMap_emb, val_searchT1_V, canonical_CimcicV]

/-- The `k`-independent re-valuation terms reconstruct `CimcicV k` from its canonical code. -/
theorem revalue_val_uCi_wCi_V (k : V) :
    revalue (uCi.val (s := stdReadingV V) ![] Empty.elim) (wCi.val (s := stdReadingV V) ![] Empty.elim)
      (canonical (CimcicV k)) = CimcicV k := by
  unfold uCi wCi
  by_cases h1 : innerCi < innerCT
  · rw [if_pos h1, if_pos h1, val_cterm_C_V, val_cterm_D_V,
      canonical_of_lt (by rw [transposeCode_CimcicV]; exact (CimcicV_lt_CimcicTV_iff k).mpr h1), revalue_zero_one]
  · rw [if_neg h1, if_neg h1]
    by_cases h2 : innerCT < innerCi
    · rw [if_pos h2, if_pos h2, val_cterm_D_V, val_cterm_C_V,
        canonical_of_gt (by rw [transposeCode_CimcicV]; exact (CimcicTV_lt_CimcicV_iff k).mpr h2)]
      exact transposeCode_transposeCode _
    · have h' : innerCi = innerCT := le_antisymm (not_lt.mp h2) (not_lt.mp h1)
      rw [if_neg h2, if_neg h2, val_numT_V, val_numT_V, Nat.cast_zero, Nat.cast_one,
        canonical_of_eq (by rw [transposeCode_CimcicV, CimcicV_eq_inner, CimcicTV_eq_inner, h']), revalue_zero_one]

/-- The transposed re-valuation terms. -/
noncomputable def uCiT : ClosedSemiterm LAct 0 := Semiterm.lMap swap uCi
noncomputable def wCiT : ClosedSemiterm LAct 0 := Semiterm.lMap swap wCi

/-- The transposed descriptions reconstruct `CimcicTV k` from the canonical code of `CimcicV k`. -/
theorem revalue_val_uCiT_wCiT_V (k : V) :
    revalue (uCiT.val (s := stdReadingV V) ![] Empty.elim) (wCiT.val (s := stdReadingV V) ![] Empty.elim)
      (canonical (CimcicV k)) = CimcicTV k := by
  unfold uCiT wCiT uCi wCi
  by_cases h1 : innerCi < innerCT
  · rw [if_pos h1, if_pos h1, lMap_swap_cterm_C, lMap_swap_cterm_D, val_cterm_D_V, val_cterm_C_V,
      canonical_of_lt (by rw [transposeCode_CimcicV]; exact (CimcicV_lt_CimcicTV_iff k).mpr h1)]
    exact transposeCode_CimcicV k
  · rw [if_neg h1, if_neg h1]
    by_cases h2 : innerCT < innerCi
    · rw [if_pos h2, if_pos h2, lMap_swap_cterm_D, lMap_swap_cterm_C, val_cterm_C_V, val_cterm_D_V,
        canonical_of_gt (by rw [transposeCode_CimcicV]; exact (CimcicTV_lt_CimcicV_iff k).mpr h2), transposeCode_CimcicV,
        revalue_zero_one]
    · have h' : innerCi = innerCT := le_antisymm (not_lt.mp h2) (not_lt.mp h1)
      have hCT : CimcicV k = CimcicTV k := by rw [CimcicV_eq_inner, CimcicTV_eq_inner, h']
      rw [if_neg h2, if_neg h2, lMap_swap_numT, lMap_swap_numT, val_numT_V, val_numT_V, Nat.cast_zero,
        Nat.cast_one, canonical_of_eq (by rw [transposeCode_CimcicV, hCT]), revalue_zero_one, hCT]

end canonical

/-! ### 3. The truth of the guard template at a frame -/

section atoms

/-- **The truth of CIMCIC's guard template at a frame**: "me plays C against opp" implies "opp plays
C against me". -/
theorem eval_templateC_V (b : Fin 6 → V) :
    Semiformula.Eval (s := stdReadingV V) b Empty.elim templateC ↔
      ((∃ n, EvalGraph n (revalue (b 1) (b 2) (b 0)) (revalue (b 4) (b 5) (b 3)) (revalue (b 1) (b 2) (b 0)) 0) →
        (∃ n, EvalGraph n (revalue (b 4) (b 5) (b 3)) (revalue (b 1) (b 2) (b 0)) (revalue (b 4) (b 5) (b 3)) 0)) := by
  rw [templateC_eq]
  simp only [LogicalConnective.HomClass.map_imply, LogicalConnective.Prop.arrow_eq,
    eval_template_plays_self_opp_V, eval_template_plays_opp_self_V, actCode, Nat.cast_zero]

/-- **The truth of the transposed guard template at a frame**: "me plays D against opp" implies
"opp plays D against me". -/
theorem eval_templateCT_V (b : Fin 6 → V) :
    Semiformula.Eval (s := stdReadingV V) b Empty.elim templateCT ↔
      ((∃ n, EvalGraph n (revalue (b 1) (b 2) (b 0)) (revalue (b 4) (b 5) (b 3)) (revalue (b 1) (b 2) (b 0)) 1) →
        (∃ n, EvalGraph n (revalue (b 4) (b 5) (b 3)) (revalue (b 1) (b 2) (b 0)) (revalue (b 4) (b 5) (b 3)) 1)) := by
  rw [templateCT_eq]
  simp only [LogicalConnective.HomClass.map_imply, LogicalConnective.Prop.arrow_eq,
    eval_template_plays_self_opp_V, eval_template_plays_opp_self_V, actCode, Nat.cast_one]

end atoms

/-! ### 4. The fixed formulas, generic in the opponent's description triple -/

section fixedFormulas

/-- **The fixed formula of CIMCIC against an opponent described by `(X, U, W)`** (`X` a one-variable
term in the budget, `U W` closed): `templateC` filled with CIMCIC's description in the me-slots. -/
noncomputable def qCG (X : Semiterm LAct Empty 1) (U W : ClosedSemiterm LAct 0) : Semisentence LAct 1 :=
  templateC ⇜ ![TCi, cl uCi, cl wCi, X, cl U, cl W]

/-- **The fixed formula of the transposed searcher** against `(X, U, W)`. -/
noncomputable def qCTG (X : Semiterm LAct Empty 1) (U W : ClosedSemiterm LAct 0) : Semisentence LAct 1 :=
  templateCT ⇜ ![TCi, cl uCiT, cl wCiT, X, cl U, cl W]

lemma lMap_swap_qCG (X : Semiterm LAct Empty 1) (U W : ClosedSemiterm LAct 0) :
    Semiformula.lMap swap (qCG X U W) =
      qCTG (Semiterm.lMap swap X) (Semiterm.lMap swap U) (Semiterm.lMap swap W) := by
  unfold qCG qCTG
  rw [Semiformula.lMap_subst, lMap_swap_templateC]
  congr 1
  funext i
  fin_cases i <;> simp [lMap_swap_TCi, lMap_swap_cl, uCiT, wCiT]

lemma lMap_swap_qCTG (X : Semiterm LAct Empty 1) (U W : ClosedSemiterm LAct 0) :
    Semiformula.lMap swap (qCTG X U W) =
      qCG (Semiterm.lMap swap X) (Semiterm.lMap swap U) (Semiterm.lMap swap W) := by
  unfold qCG qCTG
  rw [Semiformula.lMap_subst, lMap_swap_templateCT]
  congr 1
  funext i
  fin_cases i <;> simp [lMap_swap_TCi, lMap_swap_cl, uCiT, wCiT, term_lMap_swap_swap]

/-- **The truth equation of `qCG X U W` in every model** (standard reading), given that the triple
describes `opp` at the budget `k`: "`CimcicV k` plays C against `opp`" implies "`opp` plays C
against `CimcicV k`". -/
theorem eval_qCG_iff_V (k : V) (X : Semiterm LAct Empty 1) (U W : ClosedSemiterm LAct 0) {opp : V}
    (hopp : revalue (U.val (s := stdReadingV V) ![] Empty.elim) (W.val (s := stdReadingV V) ![] Empty.elim)
      (X.val (s := stdReadingV V) ![k] Empty.elim) = opp) :
    Semiformula.Eval (s := stdReadingV V) ![k] Empty.elim (qCG X U W) ↔
      ((∃ n, EvalGraph n (CimcicV k) opp (CimcicV k) 0) → (∃ n, EvalGraph n opp (CimcicV k) opp 0)) := by
  unfold qCG
  rw [Semiformula.eval_substs]
  have h0 : (Semiterm.val (s := stdReadingV V) ![k] Empty.elim ∘ ![TCi, cl uCi, cl wCi, X, cl U, cl W]) =
      ![canonical (CimcicV k), uCi.val (s := stdReadingV V) ![] Empty.elim, wCi.val (s := stdReadingV V) ![] Empty.elim,
        X.val (s := stdReadingV V) ![k] Empty.elim, U.val (s := stdReadingV V) ![] Empty.elim,
        W.val (s := stdReadingV V) ![] Empty.elim] := by
    funext i; fin_cases i <;> simp [val_TCi_V, val_cl_V]
  rw [h0, eval_templateC_V]
  simp only [Matrix.cons_val]
  rw [revalue_val_uCi_wCi_V, hopp]

/-- **The truth equation of `qCTG X U W` in every model** (standard reading): "`CimcicTV k` plays D
against `opp`" implies "`opp` plays D against `CimcicTV k`". -/
theorem eval_qCTG_iff_V (k : V) (X : Semiterm LAct Empty 1) (U W : ClosedSemiterm LAct 0) {opp : V}
    (hopp : revalue (U.val (s := stdReadingV V) ![] Empty.elim) (W.val (s := stdReadingV V) ![] Empty.elim)
      (X.val (s := stdReadingV V) ![k] Empty.elim) = opp) :
    Semiformula.Eval (s := stdReadingV V) ![k] Empty.elim (qCTG X U W) ↔
      ((∃ n, EvalGraph n (CimcicTV k) opp (CimcicTV k) 1) → (∃ n, EvalGraph n opp (CimcicTV k) opp 1)) := by
  unfold qCTG
  rw [Semiformula.eval_substs]
  have h0 : (Semiterm.val (s := stdReadingV V) ![k] Empty.elim ∘ ![TCi, cl uCiT, cl wCiT, X, cl U, cl W]) =
      ![canonical (CimcicV k), uCiT.val (s := stdReadingV V) ![] Empty.elim, wCiT.val (s := stdReadingV V) ![] Empty.elim,
        X.val (s := stdReadingV V) ![k] Empty.elim, U.val (s := stdReadingV V) ![] Empty.elim,
        W.val (s := stdReadingV V) ![] Empty.elim] := by
    funext i; fin_cases i <;> simp [val_TCi_V, val_cl_V]
  rw [h0, eval_templateCT_V]
  simp only [Matrix.cons_val]
  rw [revalue_val_uCiT_wCiT_V, hopp]

omit [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁] in
/-- The swapped reading of `qCG` is the standard reading of the transposed `qCTG`. -/
theorem eval_qCG_swap_iff_V (k : V) (X : Semiterm LAct Empty 1) (U W : ClosedSemiterm LAct 0) :
    Semiformula.Eval (s := swappedReading V) ![k] Empty.elim (qCG X U W) ↔
      Semiformula.Eval (s := stdReadingV V) ![k] Empty.elim
        (qCTG (Semiterm.lMap swap X) (Semiterm.lMap swap U) (Semiterm.lMap swap W)) := by
  rw [eval_swappedReading, lMap_swap_qCG, ← stdReadingV_eq_stdReading]

omit [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁] in
theorem eval_qCTG_swap_iff_V (k : V) (X : Semiterm LAct Empty 1) (U W : ClosedSemiterm LAct 0) :
    Semiformula.Eval (s := swappedReading V) ![k] Empty.elim (qCTG X U W) ↔
      Semiformula.Eval (s := stdReadingV V) ![k] Empty.elim
        (qCG (Semiterm.lMap swap X) (Semiterm.lMap swap U) (Semiterm.lMap swap W)) := by
  rw [eval_swappedReading, lMap_swap_qCTG, ← stdReadingV_eq_stdReading]

end fixedFormulas

/-! ### 5. The instance equations on codes, in every model -/

section instanceEq

/-- The six codes of the substituted terms of `qCG X U W`, as an internal vector. -/
noncomputable def qCGVec (X : Semiterm LAct Empty 1) (U W : ClosedSemiterm LAct 0) : V :=
  (⌜(Rew.emb TCi : SyntacticSemiterm LAct 1)⌝ : V) ∷
    ⌜(Rew.emb (cl uCi : Semiterm LAct Empty 1) : SyntacticSemiterm LAct 1)⌝ ∷
    ⌜(Rew.emb (cl wCi : Semiterm LAct Empty 1) : SyntacticSemiterm LAct 1)⌝ ∷
    ⌜(Rew.emb X : SyntacticSemiterm LAct 1)⌝ ∷
    ⌜(Rew.emb (cl U : Semiterm LAct Empty 1) : SyntacticSemiterm LAct 1)⌝ ∷
    ⌜(Rew.emb (cl W : Semiterm LAct Empty 1) : SyntacticSemiterm LAct 1)⌝ ∷ 0

lemma semitermVec_val_qCG (X : Semiterm LAct Empty 1) (U W : ClosedSemiterm LAct 0) :
    SemitermVec.val (fun i ↦ (⌜(Rew.emb ((![TCi, cl uCi, cl wCi, X, cl U, cl W] :
      Fin 6 → Semiterm LAct Empty 1) i) : SyntacticSemiterm LAct 1)⌝ : Bootstrapping.Semiterm V LAct 1)) =
      qCGVec X U W := by
  have hv : (fun i ↦ (⌜(Rew.emb ((![TCi, cl uCi, cl wCi, X, cl U, cl W] :
      Fin 6 → Semiterm LAct Empty 1) i) : SyntacticSemiterm LAct 1)⌝ : Bootstrapping.Semiterm V LAct 1)) =
      ![⌜(Rew.emb TCi : SyntacticSemiterm LAct 1)⌝,
        ⌜(Rew.emb (cl uCi : Semiterm LAct Empty 1) : SyntacticSemiterm LAct 1)⌝,
        ⌜(Rew.emb (cl wCi : Semiterm LAct Empty 1) : SyntacticSemiterm LAct 1)⌝,
        ⌜(Rew.emb X : SyntacticSemiterm LAct 1)⌝,
        ⌜(Rew.emb (cl U : Semiterm LAct Empty 1) : SyntacticSemiterm LAct 1)⌝,
        ⌜(Rew.emb (cl W : Semiterm LAct Empty 1) : SyntacticSemiterm LAct 1)⌝] := by
    funext i; fin_cases i <;> rfl
  rw [hv]
  simp only [SemitermVec.val_cons, SemitermVec.val_nil]
  rfl

/-- The code of `qCG X U W` is the internal substitution of `qCGVec X U W` into the template code. -/
theorem quote_qCG (X : Semiterm LAct Empty 1) (U W : ClosedSemiterm LAct 0) :
    (⌜qCG X U W⌝ : V) = subst LAct (qCGVec X U W) (⌜templateC⌝ : V) := by
  unfold qCG
  rw [Sentence.quote_def, Semiformula.coe_subst_eq_subst_coe, Semiformula.quote_def,
    Semiformula.typed_quote_substs, Bootstrapping.Semiformula.val_substs, ← Semiformula.quote_def,
    ← Sentence.quote_def]
  congr 1

lemma qCGVec_semitermVec (X : Semiterm LAct Empty 1) (U W : ClosedSemiterm LAct 0) :
    IsSemitermVec LAct 6 1 (qCGVec X U W : V) := by
  rw [six_eq, qCGVec]
  exact ((((((IsSemitermVec.nil 1).adjoin (semiterm_quote_emb₁ _)).adjoin (semiterm_quote_emb₁ _)).adjoin
    (semiterm_quote_emb₁ _)).adjoin (semiterm_quote_emb₁ _)).adjoin (semiterm_quote_emb₁ _)).adjoin
    (semiterm_quote_emb₁ _)

/-- Substituting `binNumeral k` into the six codes gives the description vector of `(CimcicV k, opp)`,
given that the opponent's triple describes `opp` on codes. -/
theorem termSubstVec_qCGVec (k : V) (X : Semiterm LAct Empty 1) (U W : ClosedSemiterm LAct 0) {opp : V}
    (hX : termSubst LAct (binNumeral k ∷ (0 : V)) (⌜(Rew.emb X : SyntacticSemiterm LAct 1)⌝ : V) = codeTerm (canonical opp))
    (hU : (⌜U⌝ : V) = revalueU opp) (hW : (⌜W⌝ : V) = revalueW opp) :
    termSubstVec LAct 6 (binNumeral k ∷ (0 : V)) (qCGVec X U W) = descriptions (CimcicV k) opp := by
  have hT : IsUTerm LAct (⌜(Rew.emb TCi : SyntacticSemiterm LAct 1)⌝ : V) := (semiterm_quote_emb₁ _).isUTerm
  have hU' : IsUTerm LAct (⌜(Rew.emb (cl uCi : Semiterm LAct Empty 1) : SyntacticSemiterm LAct 1)⌝ : V) :=
    (semiterm_quote_emb₁ _).isUTerm
  have hW' : IsUTerm LAct (⌜(Rew.emb (cl wCi : Semiterm LAct Empty 1) : SyntacticSemiterm LAct 1)⌝ : V) :=
    (semiterm_quote_emb₁ _).isUTerm
  have hX' : IsUTerm LAct (⌜(Rew.emb X : SyntacticSemiterm LAct 1)⌝ : V) := (semiterm_quote_emb₁ _).isUTerm
  have hU'' : IsUTerm LAct (⌜(Rew.emb (cl U : Semiterm LAct Empty 1) : SyntacticSemiterm LAct 1)⌝ : V) :=
    (semiterm_quote_emb₁ _).isUTerm
  have hW'' : IsUTerm LAct (⌜(Rew.emb (cl W : Semiterm LAct Empty 1) : SyntacticSemiterm LAct 1)⌝ : V) :=
    (semiterm_quote_emb₁ _).isUTerm
  have e0 : IsUTermVec LAct 0 (0 : V) := IsUTermVec.empty
  have e1 := e0.adjoin hW''
  have e2 := e1.adjoin hU''
  have e3 := e2.adjoin hX'
  have e4 := e3.adjoin hW'
  have e5 := e4.adjoin hU'
  have sT : termSubst LAct (binNumeral k ∷ 0) (⌜(Rew.emb TCi : SyntacticSemiterm LAct 1)⌝ : V) =
      codeTerm (canonical (CimcicV k)) := by
    rw [quote_emb_TCi, termSubst_tower, canonical_CimcicV]
  have sU : termSubst LAct (binNumeral k ∷ 0) (⌜(Rew.emb (cl uCi : Semiterm LAct Empty 1) : SyntacticSemiterm LAct 1)⌝ : V) =
      revalueU (CimcicV k) := by
    rw [quote_emb_cl_V, termSubst_closed _ (semiterm_quote_emb₀ _), revalueU_CimcicV, Semiterm.empty_quote_def]
  have sW : termSubst LAct (binNumeral k ∷ 0) (⌜(Rew.emb (cl wCi : Semiterm LAct Empty 1) : SyntacticSemiterm LAct 1)⌝ : V) =
      revalueW (CimcicV k) := by
    rw [quote_emb_cl_V, termSubst_closed _ (semiterm_quote_emb₀ _), revalueW_CimcicV, Semiterm.empty_quote_def]
  have sU2 : termSubst LAct (binNumeral k ∷ 0) (⌜(Rew.emb (cl U : Semiterm LAct Empty 1) : SyntacticSemiterm LAct 1)⌝ : V) =
      revalueU opp := by
    rw [quote_emb_cl_V, termSubst_closed _ (semiterm_quote_emb₀ _), ← Semiterm.empty_quote_def, hU]
  have sW2 : termSubst LAct (binNumeral k ∷ 0) (⌜(Rew.emb (cl W : Semiterm LAct Empty 1) : SyntacticSemiterm LAct 1)⌝ : V) =
      revalueW opp := by
    rw [quote_emb_cl_V, termSubst_closed _ (semiterm_quote_emb₀ _), ← Semiterm.empty_quote_def, hW]
  unfold qCGVec descriptions
  rw [six_eq, termSubstVec_cons hT e5, termSubstVec_cons hU' e4, termSubstVec_cons hW' e3,
    termSubstVec_cons hX' e2, termSubstVec_cons hU'' e1, termSubstVec_cons hW'' e0, termSubstVec_nil,
    sT, sU, sW, hX, sU2, sW2]

/-- **CIMCIC's instance equation on codes, in every model**: the guard code of `CimcicV k` against
`opp` is the `binNumeral k`-instance of `⌜qCG X U W⌝` whenever `(X, U, W)` describes `opp` on codes. -/
theorem guardCode_CimcicV_eq_instB (k : V) (X : Semiterm LAct Empty 1) (U W : ClosedSemiterm LAct 0) {opp : V}
    (hX : termSubst LAct (binNumeral k ∷ (0 : V)) (⌜(Rew.emb X : SyntacticSemiterm LAct 1)⌝ : V) = codeTerm (canonical opp))
    (hU : (⌜U⌝ : V) = revalueU opp) (hW : (⌜W⌝ : V) = revalueW opp) :
    guardCode (⌜templateC⌝ : V) (CimcicV k) opp = instB (⌜qCG X U W⌝ : V) k := by
  show guardCode (⌜templateC⌝ : V) (CimcicV k) opp = subst LAct (binNumeral k ∷ (0 : V)) (⌜qCG X U W⌝ : V)
  rw [quote_qCG, substs_substs (p := (⌜templateC⌝ : V)) (l := 6)
    (by simpa using Sentence.quote_isSemiformula (V := V) templateC)
    (binNumeral_cons_semitermVec k) (qCGVec_semitermVec X U W), termSubstVec_qCGVec k X U W hX hU hW]
  rfl

/-- The transposed searcher's guard code against `transposeCode opp` is the code-level τ of CIMCIC's
against `opp`. -/
lemma guardCode_CimcicTV_eq_revalue (k opp : V) :
    guardCode (⌜templateCT⌝ : V) (CimcicTV k) (transposeCode opp) =
      revalueTemplate 1 0 (guardCode (⌜templateC⌝ : V) (CimcicV k) opp) := by
  have hg0 : IsSemiformula LAct 6 (⌜templateC⌝ : V) := by
    simpa using Sentence.quote_isSemiformula (V := V) templateC
  have hg1 : IsSemiformula LAct 6 (⌜templateCT⌝ : V) := by
    simpa using Sentence.quote_isSemiformula (V := V) templateCT
  rw [← substTemplate_of_template hg0, revalueTemplate_substTemplate, transposeCode_CimcicV, revalueTemplate_quote_sentence₆_V,
    lMap_swap_templateC, substTemplate_of_template hg1]

/-- **The transposed searcher's instance equation on codes, in every model.** -/
theorem guardCode_CimcicTV_eq_instB (k : V) (X : Semiterm LAct Empty 1) (U W : ClosedSemiterm LAct 0) {opp : V}
    (hX : termSubst LAct (binNumeral k ∷ (0 : V)) (⌜(Rew.emb X : SyntacticSemiterm LAct 1)⌝ : V) = codeTerm (canonical opp))
    (hU : (⌜U⌝ : V) = revalueU opp) (hW : (⌜W⌝ : V) = revalueW opp) :
    guardCode (⌜templateCT⌝ : V) (CimcicTV k) (transposeCode opp) =
      instB (⌜qCTG (Semiterm.lMap swap X) (Semiterm.lMap swap U) (Semiterm.lMap swap W)⌝ : V) k := by
  rw [guardCode_CimcicTV_eq_revalue, guardCode_CimcicV_eq_instB k X U W hX hU hW]
  unfold instB
  rw [revalueTemplate_subst isAct_one isAct_zero (Sentence.quote_isSemiformul₁ (qCG X U W))
    (binNumeral_cons_semitermVec k), revalueTemplate_quote_sentence_V, lMap_swap_qCG]
  congr 1
  rw [show (1 : V) = 0 + 1 by simp, termRelabelVec_cons (binNumeral_term_LAct k).isUTerm IsUTermVec.empty,
    termRelabelVec_nil, termRelabel_binNumeral]

/-! #### The search clauses -/

/-- **CIMCIC's search clause in every model** (fuel `2`): a proof of its guard within the budget
makes `CimcicV k` COOPERATE (`pConst 0`). -/
theorem cimcic_search_V (k opp : V) :
    LenBox TAct k (guardCode (⌜templateC⌝ : V) (CimcicV k) opp) →
      EvalGraph 2 (CimcicV k) opp (CimcicV k) 0 := by
  intro h
  rw [show (2 : V) = 1 + 1 from one_add_one_eq_two.symm]
  show EvalGraph (1 + 1) (CimcicV k) opp (pSearch k (⌜templateC⌝ : V) (pConst 0) (pConst 1)) 0
  rw [EvalGraph.search_iff₆ (isSemiformula_quote₆ templateC)]
  left
  refine ⟨h, ?_⟩
  rw [show (1 : V) = 0 + 1 by simp, EvalGraph.const_iff]

/-- **The transposed searcher's search clause in every model** (fuel `2`): found ⇒ `D`. -/
theorem cimcicT_search_V (k opp : V) :
    LenBox TAct k (guardCode (⌜templateCT⌝ : V) (CimcicTV k) opp) →
      EvalGraph 2 (CimcicTV k) opp (CimcicTV k) 1 := by
  intro h
  rw [show (2 : V) = 1 + 1 from one_add_one_eq_two.symm]
  show EvalGraph (1 + 1) (CimcicTV k) opp (pSearch k (⌜templateCT⌝ : V) (pConst 1) (pConst 0)) 1
  rw [EvalGraph.search_iff₆ (isSemiformula_quote₆ templateCT)]
  left
  refine ⟨h, ?_⟩
  have e : EvalGraph (0 + 1) (CimcicTV k) opp (pConst 1) 1 := EvalGraph.const_iff.mpr rfl
  rwa [zero_add] at e

end instanceEq

/-! ### 6. The conjunction family, generic in the opponent -/

section conj

/-- **The Löb family of a CIMCIC cell**: CIMCIC's guard against `(X, U, W)` AND the transposed
searcher's guard against the transposed triple. -/
noncomputable def pGC (X : Semiterm LAct Empty 1) (U W : ClosedSemiterm LAct 0) : Semisentence LAct 1 :=
  qCG X U W ⋏ qCTG (Semiterm.lMap swap X) (Semiterm.lMap swap U) (Semiterm.lMap swap W)

lemma pGC_def (X : Semiterm LAct Empty 1) (U W : ClosedSemiterm LAct 0) :
    pGC X U W = qCG X U W ⋏ qCTG (Semiterm.lMap swap X) (Semiterm.lMap swap U) (Semiterm.lMap swap W) := rfl

lemma lMap_swap_pGC (X : Semiterm LAct Empty 1) (U W : ClosedSemiterm LAct 0) :
    Semiformula.lMap swap (pGC X U W) =
      qCTG (Semiterm.lMap swap X) (Semiterm.lMap swap U) (Semiterm.lMap swap W) ⋏ qCG X U W := by
  rw [pGC_def, LogicalConnective.HomClass.map_and, lMap_swap_qCG, lMap_swap_qCTG, term_lMap_swap_swap,
    term_lMap_swap_swap, term_lMap_swap_swap]

/-- **`instB ⌜pGC X U W⌝ k` is the conjunction of the two instances.** -/
theorem instB_quote_pGC (X : Semiterm LAct Empty 1) (U W : ClosedSemiterm LAct 0) (k : V) :
    instB (⌜pGC X U W⌝ : V) k =
      instB (⌜qCG X U W⌝ : V) k ^⋏
        instB (⌜qCTG (Semiterm.lMap swap X) (Semiterm.lMap swap U) (Semiterm.lMap swap W)⌝ : V) k :=
  instB_quote_and _ _ k

lemma formulaLen_instB_pGC (X : Semiterm LAct Empty 1) (U W : ClosedSemiterm LAct 0) (k : V) :
    formulaLen LAct (instB (⌜pGC X U W⌝ : V) k) =
      formulaLen LAct (instB (⌜qCG X U W⌝ : V) k) +
        formulaLen LAct (instB (⌜qCTG (Semiterm.lMap swap X) (Semiterm.lMap swap U) (Semiterm.lMap swap W)⌝ : V) k)
        + 1 := by
  rw [instB_quote_pGC,
    formulaLen_and (isFormula_instB_quote _ k).isUFormula (isFormula_instB_quote _ k).isUFormula]

/-- **Both searchers find their guards from a box of the conjunction**: for every budget `a` with
`a + 8(|qCG(k)| + |qCTG(k)|) + 7 ≤ k`, a `TAct`-proof code of the `k`-instance of `pGC` of length
`≤ a` makes `CimcicV k` cooperate with `opp` and `CimcicTV k` defect against `transposeCode opp`
(fuel 2), given the code-level description hypotheses. -/
theorem pGC_both_V (k : V) (X : Semiterm LAct Empty 1) (U W : ClosedSemiterm LAct 0) {opp : V}
    (hX : termSubst LAct (binNumeral k ∷ (0 : V)) (⌜(Rew.emb X : SyntacticSemiterm LAct 1)⌝ : V) = codeTerm (canonical opp))
    (hU : (⌜U⌝ : V) = revalueU opp) (hW : (⌜W⌝ : V) = revalueW opp) : ∀ a : V,
    a + 8 * (formulaLen LAct (instB (⌜qCG X U W⌝ : V) k) +
      formulaLen LAct (instB (⌜qCTG (Semiterm.lMap swap X) (Semiterm.lMap swap U) (Semiterm.lMap swap W)⌝ : V) k))
      + 7 ≤ k →
    LenBoxUnbounded TAct a (instB (⌜pGC X U W⌝ : V) k) →
    EvalGraph 2 (CimcicV k) opp (CimcicV k) 0 ∧ EvalGraph 2 (CimcicTV k) (transposeCode opp) (CimcicTV k) 1 := by
  intro a ha h
  rw [instB_quote_pGC] at h
  have hx := isFormula_instB_quote (qCG X U W) k
  have hy := isFormula_instB_quote (qCTG (Semiterm.lMap swap X) (Semiterm.lMap swap U) (Semiterm.lMap swap W)) k
  have h₁ := lenBoxUnbounded_mono_V ha (lenBoxUnbounded_andL_V hx hy h)
  have h₂ := lenBoxUnbounded_mono_V ha (lenBoxUnbounded_andR_V hx hy h)
  rw [lenBoxUnbounded_iff_lenBox, ← guardCode_CimcicV_eq_instB k X U W hX hU hW] at h₁
  rw [lenBoxUnbounded_iff_lenBox, ← guardCode_CimcicTV_eq_instB k X U W hX hU hW] at h₂
  exact ⟨cimcic_search_V k opp h₁, cimcicT_search_V k _ h₂⟩

/-- **Both searchers FIND their guards** (the box form of `pGC_both_V`). -/
theorem pGC_guards_V (k : V) (X : Semiterm LAct Empty 1) (U W : ClosedSemiterm LAct 0) {opp : V}
    (hX : termSubst LAct (binNumeral k ∷ (0 : V)) (⌜(Rew.emb X : SyntacticSemiterm LAct 1)⌝ : V) = codeTerm (canonical opp))
    (hU : (⌜U⌝ : V) = revalueU opp) (hW : (⌜W⌝ : V) = revalueW opp) (a : V)
    (ha : a + 8 * (formulaLen LAct (instB (⌜qCG X U W⌝ : V) k) +
      formulaLen LAct (instB (⌜qCTG (Semiterm.lMap swap X) (Semiterm.lMap swap U) (Semiterm.lMap swap W)⌝ : V) k))
      + 7 ≤ k)
    (hpc : LenBoxUnbounded TAct a (instB (⌜pGC X U W⌝ : V) k)) :
    LenBox TAct k (guardCode (⌜templateC⌝ : V) (CimcicV k) opp) ∧
    LenBox TAct k (guardCode (⌜templateCT⌝ : V) (CimcicTV k) (transposeCode opp)) := by
  rw [instB_quote_pGC] at hpc
  have hx := isFormula_instB_quote (qCG X U W) k
  have hy := isFormula_instB_quote (qCTG (Semiterm.lMap swap X) (Semiterm.lMap swap U) (Semiterm.lMap swap W)) k
  have h₁ := lenBoxUnbounded_mono_V ha (lenBoxUnbounded_andL_V hx hy hpc)
  have h₂ := lenBoxUnbounded_mono_V ha (lenBoxUnbounded_andR_V hx hy hpc)
  rw [lenBoxUnbounded_iff_lenBox, ← guardCode_CimcicV_eq_instB k X U W hX hU hW] at h₁
  rw [lenBoxUnbounded_iff_lenBox, ← guardCode_CimcicTV_eq_instB k X U W hX hU hW] at h₂
  exact ⟨h₁, h₂⟩

/-! #### `pGC` in both readings -/

/-- `pGC(k)` in the standard reading, given that the triple describes `opp` and the transposed
triple describes `opp'` (in every intended instance, `opp' = transposeCode opp`). -/
theorem eval_pGC_iff_std (k : V) (X : Semiterm LAct Empty 1) (U W : ClosedSemiterm LAct 0) {opp opp' : V}
    (hopp : revalue (U.val (s := stdReadingV V) ![] Empty.elim) (W.val (s := stdReadingV V) ![] Empty.elim)
      (X.val (s := stdReadingV V) ![k] Empty.elim) = opp)
    (hopp' : revalue ((Semiterm.lMap swap U).val (s := stdReadingV V) ![] Empty.elim)
      ((Semiterm.lMap swap W).val (s := stdReadingV V) ![] Empty.elim)
      ((Semiterm.lMap swap X).val (s := stdReadingV V) ![k] Empty.elim) = opp') :
    Semiformula.Eval (s := stdReadingV V) ![k] Empty.elim (pGC X U W) ↔
      ((∃ n, EvalGraph n (CimcicV k) opp (CimcicV k) 0) → (∃ n, EvalGraph n opp (CimcicV k) opp 0)) ∧
      ((∃ n, EvalGraph n (CimcicTV k) opp' (CimcicTV k) 1) → (∃ n, EvalGraph n opp' (CimcicTV k) opp' 1)) := by
  rw [pGC_def]
  simp only [LogicalConnective.HomClass.map_and, LogicalConnective.Prop.and_eq]
  rw [eval_qCG_iff_V k X U W hopp, eval_qCTG_iff_V k _ _ _ hopp']

/-- `pGC(k)` in the swapped reading: the SAME content (the conjuncts exchange roles). -/
theorem eval_pGC_iff_swap (k : V) (X : Semiterm LAct Empty 1) (U W : ClosedSemiterm LAct 0) {opp opp' : V}
    (hopp : revalue (U.val (s := stdReadingV V) ![] Empty.elim) (W.val (s := stdReadingV V) ![] Empty.elim)
      (X.val (s := stdReadingV V) ![k] Empty.elim) = opp)
    (hopp' : revalue ((Semiterm.lMap swap U).val (s := stdReadingV V) ![] Empty.elim)
      ((Semiterm.lMap swap W).val (s := stdReadingV V) ![] Empty.elim)
      ((Semiterm.lMap swap X).val (s := stdReadingV V) ![k] Empty.elim) = opp') :
    Semiformula.Eval (s := swappedReading V) ![k] Empty.elim (pGC X U W) ↔
      ((∃ n, EvalGraph n (CimcicV k) opp (CimcicV k) 0) → (∃ n, EvalGraph n opp (CimcicV k) opp 0)) ∧
      ((∃ n, EvalGraph n (CimcicTV k) opp' (CimcicTV k) 1) → (∃ n, EvalGraph n opp' (CimcicTV k) opp' 1)) := by
  rw [eval_swappedReading, lMap_swap_pGC, ← stdReadingV_eq_stdReading]
  simp only [LogicalConnective.HomClass.map_and, LogicalConnective.Prop.and_eq]
  rw [eval_qCG_iff_V k X U W hopp, eval_qCTG_iff_V k _ _ _ hopp', and_comm]

/-- `pGC(k)` in the standard reading, `stdReading` form. -/
theorem eval_pGC_iff_stdReading (k : V) (X : Semiterm LAct Empty 1) (U W : ClosedSemiterm LAct 0) {opp opp' : V}
    (hopp : revalue (U.val (s := stdReadingV V) ![] Empty.elim) (W.val (s := stdReadingV V) ![] Empty.elim)
      (X.val (s := stdReadingV V) ![k] Empty.elim) = opp)
    (hopp' : revalue ((Semiterm.lMap swap U).val (s := stdReadingV V) ![] Empty.elim)
      ((Semiterm.lMap swap W).val (s := stdReadingV V) ![] Empty.elim)
      ((Semiterm.lMap swap X).val (s := stdReadingV V) ![k] Empty.elim) = opp') :
    Semiformula.Eval (s := stdReading V) ![k] Empty.elim (pGC X U W) ↔
      ((∃ n, EvalGraph n (CimcicV k) opp (CimcicV k) 0) → (∃ n, EvalGraph n opp (CimcicV k) opp 0)) ∧
      ((∃ n, EvalGraph n (CimcicTV k) opp' (CimcicTV k) 1) → (∃ n, EvalGraph n opp' (CimcicTV k) opp' 1)) := by
  rw [← stdReadingV_eq_stdReading]; exact eval_pGC_iff_std k X U W hopp hopp'

end conj

/-! ### 7. Cell 1 — CIMCIC × Dupoc `(C, C)`, the MUTUAL family -/

section dupocCell

/-! #### The description hypotheses: CIMCIC's own triple, Dupoc's triple -/

/-- CIMCIC's own triple describes `CimcicV k` on codes: the `X`-hypothesis. -/
lemma hX_cimcic (k : V) :
    termSubst LAct (binNumeral k ∷ (0 : V)) (⌜(Rew.emb TCi : SyntacticSemiterm LAct 1)⌝ : V) =
      codeTerm (canonical (CimcicV k)) := by
  rw [quote_emb_TCi, termSubst_tower, canonical_CimcicV]

lemma hU_cimcic (k : V) : (⌜uCi⌝ : V) = revalueU (CimcicV k) := (revalueU_CimcicV k).symm
lemma hW_cimcic (k : V) : (⌜wCi⌝ : V) = revalueW (CimcicV k) := (revalueW_CimcicV k).symm

/-- CIMCIC's own triple describes `CimcicV k` in `stdReadingV V`. -/
lemma desc_cimcic (k : V) :
    revalue (uCi.val (s := stdReadingV V) ![] Empty.elim) (wCi.val (s := stdReadingV V) ![] Empty.elim)
      (TCi.val (s := stdReadingV V) ![k] Empty.elim) = CimcicV k := by
  rw [val_TCi_V]; exact revalue_val_uCi_wCi_V k

/-- The transposed triple describes `CimcicTV k` in `stdReadingV V`. -/
lemma descT_cimcic (k : V) :
    revalue ((Semiterm.lMap swap uCi).val (s := stdReadingV V) ![] Empty.elim)
      ((Semiterm.lMap swap wCi).val (s := stdReadingV V) ![] Empty.elim)
      ((Semiterm.lMap swap TCi).val (s := stdReadingV V) ![k] Empty.elim) = CimcicTV k := by
  rw [lMap_swap_TCi, val_TCi_V]; exact revalue_val_uCiT_wCiT_V k

/-- Dupoc's triple `(TD, uD, wD)` describes `DupocV k` in `stdReadingV V`. -/
lemma desc_dupoc (k : V) :
    revalue (uD.val (s := stdReadingV V) ![] Empty.elim) (wD.val (s := stdReadingV V) ![] Empty.elim)
      (TD.val (s := stdReadingV V) ![k] Empty.elim) = DupocV k := by
  rw [val_TD_V]; exact revalue_val_uD_wD_V k

/-- The transposed triple describes `CupodV k` in `stdReadingV V` (`uC = swap uD`, `wC = swap wD`). -/
lemma descT_dupoc (k : V) :
    revalue ((Semiterm.lMap swap uD).val (s := stdReadingV V) ![] Empty.elim)
      ((Semiterm.lMap swap wD).val (s := stdReadingV V) ![] Empty.elim)
      ((Semiterm.lMap swap TD).val (s := stdReadingV V) ![k] Empty.elim) = CupodV k := by
  rw [lMap_swap_TD, val_TD_V]
  exact revalue_val_uC_wC_V k

/-! #### The two fixed formulas of the cell -/

/-- **CIMCIC's guard against Dupoc**: `qCDu(k)` says "`CimcicV k` plays C against `DupocV k` implies
`DupocV k` plays C against `CimcicV k`". -/
noncomputable def qCDu : Semisentence LAct 1 := qCG TD uD wD

lemma qCDu_def : qCDu = qCG TD uD wD := rfl

/-- **The instance equation on codes**: CIMCIC's guard code against `DupocV k`. -/
theorem guardCode_CimcicV_DupocV_eq_instB (k : V) :
    guardCode (⌜templateC⌝ : V) (CimcicV k) (DupocV k) = instB (⌜qCDu⌝ : V) k :=
  guardCode_CimcicV_eq_instB k TD uD wD (hX_dupoc k) (hU_dupoc k) (hW_dupoc k)

/-- **The truth equation of `qCDu` in every model** (standard reading). -/
theorem eval_qCDu_iff_V (k : V) :
    Semiformula.Eval (s := stdReadingV V) ![k] Empty.elim qCDu ↔
      ((∃ n, EvalGraph n (CimcicV k) (DupocV k) (CimcicV k) 0) → (∃ n, EvalGraph n (DupocV k) (CimcicV k) (DupocV k) 0)) :=
  eval_qCG_iff_V k TD uD wD (desc_dupoc k)

/-- **The truth equation of `qCDu` in the swapped reading**: the transposed searcher against Cupod,
"D implies Cupod plays D". -/
theorem eval_qCDu_swap_iff_V (k : V) :
    Semiformula.Eval (s := swappedReading V) ![k] Empty.elim qCDu ↔
      ((∃ n, EvalGraph n (CimcicTV k) (CupodV k) (CimcicTV k) 1) → (∃ n, EvalGraph n (CupodV k) (CimcicTV k) (CupodV k) 1)) := by
  rw [qCDu_def, eval_qCG_swap_iff_V]
  exact eval_qCTG_iff_V k _ _ _ (descT_dupoc k)

/-- **Dupoc's guard against CIMCIC**: `qDCi(k)` says "`CimcicV k` plays C against `DupocV k`" — the
hand-written template `guardTemplate 0` filled with Dupoc's triple (me) and CIMCIC's triple (opp). -/
noncomputable def qDCi : Semisentence LAct 1 := qG 0 TD uD wD TCi uCi wCi

lemma qDCi_def : qDCi = qG 0 TD uD wD TCi uCi wCi := rfl

/-- **The instance equation on codes**: Dupoc's guard code against `CimcicV k`. -/
theorem guardCode_DupocV_CimcicV_eq_instB (k : V) :
    guardCode (⌜guardTemplate 0⌝ : V) (DupocV k) (CimcicV k) = instB (⌜qDCi⌝ : V) k :=
  guardCode_GtmplA_eq_instB 0 k TD uD wD TCi uCi wCi (hX_dupoc k) (hU_dupoc k) (hW_dupoc k)
    (hX_cimcic k) (hU_cimcic k) (hW_cimcic k)

/-- **The transposed instance equation**: Cupod's guard code against `CimcicTV k` is the
`binNumeral k`-instance of `⌜lMap swap qDCi⌝`. -/
theorem guardCode_CupodV_CimcicTV_eq_instB (k : V) :
    guardCode (⌜guardTemplate 1⌝ : V) (CupodV k) (CimcicTV k) = instB (⌜Semiformula.lMap swap qDCi⌝ : V) k := by
  have h := guardCode_GtmplA_swap_eq_instB 0 k TD uD wD TCi uCi wCi (hX_dupoc k) (hU_dupoc k) (hW_dupoc k)
    (hX_cimcic k) (hU_cimcic k) (hW_cimcic k)
  rwa [swapAction_zero, transposeCode_DupocV, transposeCode_CimcicV] at h

/-- **The truth equation of `qDCi` in every model** (standard reading). -/
theorem eval_qDCi_iff_V (k : V) :
    Semiformula.Eval (s := stdReadingV V) ![k] Empty.elim qDCi ↔
      ∃ n, EvalGraph n (CimcicV k) (DupocV k) (CimcicV k) 0 := by
  have h := eval_qG_iff_V 0 k TD uD wD TCi uCi wCi (desc_dupoc k) (desc_cimcic k)
  rwa [Nat.cast_zero] at h

/-- **The truth equation of `lMap swap qDCi` in every model** (standard reading): "`CimcicTV k` plays
D against `CupodV k`". -/
theorem eval_qDCi_swapped_iff_V (k : V) :
    Semiformula.Eval (s := stdReadingV V) ![k] Empty.elim (Semiformula.lMap swap qDCi) ↔
      ∃ n, EvalGraph n (CimcicTV k) (CupodV k) (CimcicTV k) 1 := by
  rw [qDCi_def, lMap_swap_qG, swapAction_zero]
  have h := eval_qG_iff_V 1 k _ _ _ _ _ _ (descT_dupoc k) (descT_cimcic k)
  rwa [Nat.cast_one] at h

/-! #### The mutual family -/

/-- The two-sided conjunct of the mutual family: Dupoc's guard against CIMCIC and its transposition. -/
noncomputable def pDCi : Semisentence LAct 1 := qDCi ⋏ Semiformula.lMap swap qDCi

lemma pDCi_def : pDCi = qDCi ⋏ Semiformula.lMap swap qDCi := rfl

lemma lMap_swap_pDCi : Semiformula.lMap swap pDCi = Semiformula.lMap swap qDCi ⋏ qDCi := by
  rw [pDCi_def, LogicalConnective.HomClass.map_and, lMap_swap_swap]

/-- **The MUTUAL Löb family of the CIMCIC × Dupoc cell**: CIMCIC's family against Dupoc's triple (and
the transposed searcher's against Cupod's) AND Dupoc's guard against CIMCIC (and its transposition) —
four guards, each searcher's box supplied by the same conjunction. -/
noncomputable def pCiD : Semisentence LAct 1 := pGC TD uD wD ⋏ pDCi

lemma pCiD_def : pCiD = pGC TD uD wD ⋏ pDCi := rfl

theorem instB_quote_pDCi (k : V) :
    instB (⌜pDCi⌝ : V) k = instB (⌜qDCi⌝ : V) k ^⋏ instB (⌜Semiformula.lMap swap qDCi⌝ : V) k :=
  instB_quote_and _ _ k

theorem instB_quote_pCiD (k : V) :
    instB (⌜pCiD⌝ : V) k = instB (⌜pGC TD uD wD⌝ : V) k ^⋏ instB (⌜pDCi⌝ : V) k :=
  instB_quote_and _ _ k

lemma formulaLen_instB_pDCi (k : V) :
    formulaLen LAct (instB (⌜pDCi⌝ : V) k) =
      formulaLen LAct (instB (⌜qDCi⌝ : V) k) + formulaLen LAct (instB (⌜Semiformula.lMap swap qDCi⌝ : V) k) + 1 := by
  rw [instB_quote_pDCi,
    formulaLen_and (isFormula_instB_quote _ k).isUFormula (isFormula_instB_quote _ k).isUFormula]

lemma formulaLen_instB_pCiD (k : V) :
    formulaLen LAct (instB (⌜pCiD⌝ : V) k) =
      formulaLen LAct (instB (⌜pGC TD uD wD⌝ : V) k) + formulaLen LAct (instB (⌜pDCi⌝ : V) k) + 1 := by
  rw [instB_quote_pCiD,
    formulaLen_and (isFormula_instB_quote _ k).isUFormula (isFormula_instB_quote _ k).isUFormula]

/-- **All four searchers find their guards from a box of the mutual family** (fuel 2): CIMCIC
cooperates with Dupoc, the transposed searcher defects against Cupod, Dupoc cooperates with CIMCIC,
Cupod defects against the transposed searcher. -/
theorem pCiD_all_V (k a : V)
    (ha₁ : a + 8 * (formulaLen LAct (instB (⌜pGC TD uD wD⌝ : V) k) + formulaLen LAct (instB (⌜pDCi⌝ : V) k)) + 7 +
      8 * (formulaLen LAct (instB (⌜qCG TD uD wD⌝ : V) k) +
        formulaLen LAct (instB (⌜qCTG (Semiterm.lMap swap TD) (Semiterm.lMap swap uD) (Semiterm.lMap swap wD)⌝ : V) k))
      + 7 ≤ k)
    (ha₂ : a + 8 * (formulaLen LAct (instB (⌜pGC TD uD wD⌝ : V) k) + formulaLen LAct (instB (⌜pDCi⌝ : V) k)) + 7 +
      8 * (formulaLen LAct (instB (⌜qDCi⌝ : V) k) + formulaLen LAct (instB (⌜Semiformula.lMap swap qDCi⌝ : V) k))
      + 7 ≤ k)
    (h : LenBoxUnbounded TAct a (instB (⌜pCiD⌝ : V) k)) :
    (EvalGraph 2 (CimcicV k) (DupocV k) (CimcicV k) 0 ∧ EvalGraph 2 (CimcicTV k) (CupodV k) (CimcicTV k) 1) ∧
    (EvalGraph 2 (DupocV k) (CimcicV k) (DupocV k) 0 ∧ EvalGraph 2 (CupodV k) (CimcicTV k) (CupodV k) 1) := by
  rw [instB_quote_pCiD] at h
  have hx := isFormula_instB_quote (pGC TD uD wD) k
  have hy := isFormula_instB_quote pDCi k
  have h₁ := lenBoxUnbounded_andL_V hx hy h
  have h₂ := lenBoxUnbounded_andR_V hx hy h
  obtain ⟨g1, g2⟩ := pGC_both_V k TD uD wD (hX_dupoc k) (hU_dupoc k) (hW_dupoc k) _ ha₁ h₁
  rw [transposeCode_DupocV] at g2
  have hx' := isFormula_instB_quote qDCi k
  have hy' := isFormula_instB_quote (Semiformula.lMap swap qDCi) k
  have h₂' : LenBoxUnbounded TAct
      (a + 8 * (formulaLen LAct (instB (⌜pGC TD uD wD⌝ : V) k) + formulaLen LAct (instB (⌜pDCi⌝ : V) k)) + 7)
      (instB (⌜qDCi⌝ : V) k ^⋏ instB (⌜Semiformula.lMap swap qDCi⌝ : V) k) := by
    rw [← instB_quote_pDCi]; exact h₂
  have c1 := lenBoxUnbounded_mono_V ha₂ (lenBoxUnbounded_andL_V hx' hy' h₂')
  have c2 := lenBoxUnbounded_mono_V ha₂ (lenBoxUnbounded_andR_V hx' hy' h₂')
  rw [lenBoxUnbounded_iff_lenBox, ← guardCode_DupocV_CimcicV_eq_instB] at c1
  rw [lenBoxUnbounded_iff_lenBox, ← guardCode_CupodV_CimcicTV_eq_instB] at c2
  exact ⟨⟨g1, g2⟩, ⟨dupoc_search_any_V k _ c1, cupod_search_any_V k _ c2⟩⟩

/-- **The box form**: the two guards of the cell are provable within `k`. -/
theorem pCiD_guards_V (k a : V)
    (ha₁ : a + 8 * (formulaLen LAct (instB (⌜pGC TD uD wD⌝ : V) k) + formulaLen LAct (instB (⌜pDCi⌝ : V) k)) + 7 +
      8 * (formulaLen LAct (instB (⌜qCG TD uD wD⌝ : V) k) +
        formulaLen LAct (instB (⌜qCTG (Semiterm.lMap swap TD) (Semiterm.lMap swap uD) (Semiterm.lMap swap wD)⌝ : V) k))
      + 7 ≤ k)
    (ha₂ : a + 8 * (formulaLen LAct (instB (⌜pGC TD uD wD⌝ : V) k) + formulaLen LAct (instB (⌜pDCi⌝ : V) k)) + 7 +
      8 * (formulaLen LAct (instB (⌜qDCi⌝ : V) k) + formulaLen LAct (instB (⌜Semiformula.lMap swap qDCi⌝ : V) k))
      + 7 ≤ k)
    (h : LenBoxUnbounded TAct a (instB (⌜pCiD⌝ : V) k)) :
    LenBox TAct k (guardCode (⌜templateC⌝ : V) (CimcicV k) (DupocV k)) ∧
    LenBox TAct k (guardCode (⌜guardTemplate 0⌝ : V) (DupocV k) (CimcicV k)) := by
  rw [instB_quote_pCiD] at h
  have hx := isFormula_instB_quote (pGC TD uD wD) k
  have hy := isFormula_instB_quote pDCi k
  have h₁ := lenBoxUnbounded_andL_V hx hy h
  have h₂ := lenBoxUnbounded_andR_V hx hy h
  obtain ⟨g1, _⟩ := pGC_guards_V k TD uD wD (hX_dupoc k) (hU_dupoc k) (hW_dupoc k) _ ha₁ h₁
  have hx' := isFormula_instB_quote qDCi k
  have hy' := isFormula_instB_quote (Semiformula.lMap swap qDCi) k
  have h₂' : LenBoxUnbounded TAct
      (a + 8 * (formulaLen LAct (instB (⌜pGC TD uD wD⌝ : V) k) + formulaLen LAct (instB (⌜pDCi⌝ : V) k)) + 7)
      (instB (⌜qDCi⌝ : V) k ^⋏ instB (⌜Semiformula.lMap swap qDCi⌝ : V) k) := by
    rw [← instB_quote_pDCi]; exact h₂
  have c1 := lenBoxUnbounded_mono_V ha₂ (lenBoxUnbounded_andL_V hx' hy' h₂')
  rw [lenBoxUnbounded_iff_lenBox, ← guardCode_DupocV_CimcicV_eq_instB] at c1
  exact ⟨g1, c1⟩

/-! #### `pCiD` in both readings -/

/-- `pCiD(k)` in the standard reading. -/
theorem eval_pCiD_iff_std (k : V) :
    Semiformula.Eval (s := stdReadingV V) ![k] Empty.elim pCiD ↔
      (((∃ n, EvalGraph n (CimcicV k) (DupocV k) (CimcicV k) 0) → (∃ n, EvalGraph n (DupocV k) (CimcicV k) (DupocV k) 0)) ∧
       ((∃ n, EvalGraph n (CimcicTV k) (CupodV k) (CimcicTV k) 1) → (∃ n, EvalGraph n (CupodV k) (CimcicTV k) (CupodV k) 1))) ∧
      ((∃ n, EvalGraph n (CimcicV k) (DupocV k) (CimcicV k) 0) ∧ (∃ n, EvalGraph n (CimcicTV k) (CupodV k) (CimcicTV k) 1)) := by
  rw [pCiD_def, pDCi_def]
  simp only [LogicalConnective.HomClass.map_and, LogicalConnective.Prop.and_eq]
  rw [eval_pGC_iff_std k TD uD wD (desc_dupoc k) (descT_dupoc k), eval_qDCi_iff_V, eval_qDCi_swapped_iff_V]

/-- `pCiD(k)` in the swapped reading: the SAME content (the conjuncts exchange roles). -/
theorem eval_pCiD_iff_swap (k : V) :
    Semiformula.Eval (s := swappedReading V) ![k] Empty.elim pCiD ↔
      (((∃ n, EvalGraph n (CimcicV k) (DupocV k) (CimcicV k) 0) → (∃ n, EvalGraph n (DupocV k) (CimcicV k) (DupocV k) 0)) ∧
       ((∃ n, EvalGraph n (CimcicTV k) (CupodV k) (CimcicTV k) 1) → (∃ n, EvalGraph n (CupodV k) (CimcicTV k) (CupodV k) 1))) ∧
      ((∃ n, EvalGraph n (CimcicV k) (DupocV k) (CimcicV k) 0) ∧ (∃ n, EvalGraph n (CimcicTV k) (CupodV k) (CimcicTV k) 1)) := by
  rw [eval_swappedReading, pCiD_def, LogicalConnective.HomClass.map_and, lMap_swap_pGC, lMap_swap_pDCi, ← stdReadingV_eq_stdReading]
  simp only [LogicalConnective.HomClass.map_and, LogicalConnective.Prop.and_eq]
  rw [eval_qCG_iff_V k TD uD wD (desc_dupoc k), eval_qCTG_iff_V k _ _ _ (descT_dupoc k), eval_qDCi_iff_V,
    eval_qDCi_swapped_iff_V, and_comm (a := ∃ n, EvalGraph n (CimcicTV k) (CupodV k) (CimcicTV k) 1),
    and_comm (a := (∃ n, EvalGraph n (CimcicTV k) (CupodV k) (CimcicTV k) 1) → _)]

theorem eval_pCiD_iff_stdReading (k : V) :
    Semiformula.Eval (s := stdReading V) ![k] Empty.elim pCiD ↔
      (((∃ n, EvalGraph n (CimcicV k) (DupocV k) (CimcicV k) 0) → (∃ n, EvalGraph n (DupocV k) (CimcicV k) (DupocV k) 0)) ∧
       ((∃ n, EvalGraph n (CimcicTV k) (CupodV k) (CimcicTV k) 1) → (∃ n, EvalGraph n (CupodV k) (CimcicTV k) (CupodV k) 1))) ∧
      ((∃ n, EvalGraph n (CimcicV k) (DupocV k) (CimcicV k) 0) ∧ (∃ n, EvalGraph n (CimcicTV k) (CupodV k) (CimcicTV k) 1)) := by
  rw [← stdReadingV_eq_stdReading]; exact eval_pCiD_iff_std k

/-! #### The Löb premise and the cells -/

/-- **The bounded Löb premise of the mutual family, slack `(14, 16)`**: a box of `pCiD(k)` makes all four
searchers find their guards (fuel 2); CIMCIC's implications hold because Dupoc/Cupod actually play the
consequents, and Dupoc's/Cupod's guards are the plays of CIMCIC/its transposition — true in both
readings. -/
theorem loebSound_pCiD : LoebSound pCiD 14 16 := by
  intro V _ _ k a ha h
  have : V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁ := inferInstance
  have ha₁ := le_trans (slack4_le a _ _ _ _ _ (formulaLen_instB_pGC TD uD wD k) (formulaLen_instB_pCiD k)) ha
  have ha₂ := le_trans (slack4_le' a _ _ _ _ _ (formulaLen_instB_pDCi k) (formulaLen_instB_pCiD k)) ha
  obtain ⟨⟨g1, g2⟩, ⟨c1, c2⟩⟩ := pCiD_all_V k a ha₁ ha₂ h
  exact ⟨(eval_pCiD_iff_stdReading k).mpr ⟨⟨fun _ ↦ ⟨2, c1⟩, fun _ ↦ ⟨2, c2⟩⟩, ⟨⟨2, g1⟩, ⟨2, g2⟩⟩⟩,
    (eval_pCiD_iff_swap k).mpr ⟨⟨fun _ ↦ ⟨2, c1⟩, fun _ ↦ ⟨2, c2⟩⟩, ⟨⟨2, g1⟩, ⟨2, g2⟩⟩⟩⟩

/-- **The CIMCIC × Dupoc cell, packaged**: for all large `k`, CIMCIC cooperates with Dupoc and Dupoc
cooperates with CIMCIC (fuel 2), and both guard boxes hold. -/
theorem loeb_Cimcic_vs_Dupoc_core_of_nec {d : ℕ} (hE : BoundedInnerNec d) :
    ∃ k₀ : ℕ, ∀ k : ℕ, k₀ < k →
      (EvalGraph 2 (Cimcic k) (Dupoc k) (Cimcic k) 0 ∧ EvalGraph 2 (Dupoc k) (Cimcic k) (Dupoc k) 0) ∧
      (LenBox TAct k (guardCode (⌜templateC⌝ : ℕ) (Cimcic k) (Dupoc k)) ∧
        LenBox TAct k (guardCode (⌜guardTemplate 0⌝ : ℕ) (Dupoc k) (Cimcic k))) := by
  obtain ⟨k₀, h⟩ := family_found pCiD hE loebSound_pCiD
  refine ⟨k₀, fun k hk ↦ ?_⟩
  obtain ⟨a, ha, hpc⟩ := h k hk
  have ha₁ := le_def.mpr (slack4_nat a _ _ _ _ _ k (formulaLen_instB_pGC (V := ℕ) TD uD wD k)
    (formulaLen_instB_pCiD (V := ℕ) k) ha)
  have ha₂ := le_def.mpr (slack4_nat' a _ _ _ _ _ k (formulaLen_instB_pDCi (V := ℕ) k)
    (formulaLen_instB_pCiD (V := ℕ) k) ha)
  obtain ⟨⟨g1, _⟩, ⟨c1, _⟩⟩ := pCiD_all_V (V := ℕ) k a ha₁ ha₂ hpc
  exact ⟨⟨g1, c1⟩, pCiD_guards_V (V := ℕ) k a ha₁ ha₂ hpc⟩

/-- **CIMCIC × Dupoc is `(C, C)` in PA-`S'`, conditional on bounded inner necessitation**: for all
large `k`, `Cimcic k` cooperates with `Dupoc k` and `Dupoc k` cooperates with `Cimcic k` (fuel 2). -/
theorem loeb_Cimcic_vs_Dupoc_of_nec {d : ℕ} (hE : BoundedInnerNec d) :
    ∃ k₀ : ℕ, ∀ k : ℕ, k₀ < k →
      EvalGraph 2 (Cimcic k) (Dupoc k) (Cimcic k) 0 ∧ EvalGraph 2 (Dupoc k) (Cimcic k) (Dupoc k) 0 := by
  obtain ⟨k₀, h⟩ := loeb_Cimcic_vs_Dupoc_core_of_nec hE
  exact ⟨k₀, fun k hk ↦ (h k hk).1⟩

/-- **The box form**: for all large `k`, both CIMCIC and Dupoc FIND their guards against each other
within the budget `k` (conditional). -/
theorem loeb_Cimcic_vs_Dupoc_guards_of_nec {d : ℕ} (hE : BoundedInnerNec d) :
    ∃ k₀ : ℕ, ∀ k : ℕ, k₀ < k →
      LenBox TAct k (guardCode (⌜templateC⌝ : ℕ) (Cimcic k) (Dupoc k)) ∧
      LenBox TAct k (guardCode (⌜guardTemplate 0⌝ : ℕ) (Dupoc k) (Cimcic k)) := by
  obtain ⟨k₀, h⟩ := loeb_Cimcic_vs_Dupoc_core_of_nec hE
  exact ⟨k₀, fun k hk ↦ (h k hk).2⟩

/-- **CIMCIC × Dupoc `(C, C)` in PA-`S'`, unconditional.** -/
theorem loeb_Cimcic_vs_Dupoc :
    ∃ k₀ : ℕ, ∀ k : ℕ, k₀ < k →
      EvalGraph 2 (Cimcic k) (Dupoc k) (Cimcic k) 0 ∧ EvalGraph 2 (Dupoc k) (Cimcic k) (Dupoc k) 0 :=
  loeb_Cimcic_vs_Dupoc_of_nec boundedInnerNec_sixteen

/-- **CIMCIC and Dupoc find their guards against each other, unconditional.** -/
theorem loeb_Cimcic_vs_Dupoc_guards :
    ∃ k₀ : ℕ, ∀ k : ℕ, k₀ < k →
      LenBox TAct k (guardCode (⌜templateC⌝ : ℕ) (Cimcic k) (Dupoc k)) ∧
      LenBox TAct k (guardCode (⌜guardTemplate 0⌝ : ℕ) (Dupoc k) (Cimcic k)) :=
  loeb_Cimcic_vs_Dupoc_guards_of_nec boundedInnerNec_sixteen

end dupocCell

/-! ### 8. Cell 2 — CIMCIC × Mirror `(C, C)` -/

section mirrorCell

/-- **The fixed formula of CIMCIC against Mirror**: `qCMi(k)` says "`CimcicV k` plays C against
Mirror implies Mirror plays C against `CimcicV k`". -/
noncomputable def qCMi : Semisentence LAct 1 := qCG (cl TM) (numT 0) (numT 1)

lemma qCMi_def : qCMi = qCG (cl TM) (numT 0) (numT 1) := rfl

/-- **The instance equation on codes**: CIMCIC's guard code against Mirror is the `binNumeral k`-instance
of `⌜qCMi⌝`, in every model. -/
theorem guardCode_CimcicV_MirrorV_eq_instB (k : V) :
    guardCode (⌜templateC⌝ : V) (CimcicV k) MirrorV = instB (⌜qCMi⌝ : V) k :=
  guardCode_CimcicV_eq_instB k (cl TM) (numT 0) (numT 1) (hX_mirror k) hU_mirror hW_mirror

/-- **The truth equation of `qCMi` in every model** (standard reading). -/
theorem eval_qCMi_iff_V (k : V) :
    Semiformula.Eval (s := stdReadingV V) ![k] Empty.elim qCMi ↔
      ((∃ n, EvalGraph n (CimcicV k) MirrorV (CimcicV k) 0) → (∃ n, EvalGraph n MirrorV (CimcicV k) MirrorV 0)) :=
  eval_qCG_iff_V k (cl TM) (numT 0) (numT 1) (desc_mirror k)

/-- **The truth equation of `qCMi` in the swapped reading**: the transposed searcher against Mirror,
"D implies Mirror plays D". -/
theorem eval_qCMi_swap_iff_V (k : V) :
    Semiformula.Eval (s := swappedReading V) ![k] Empty.elim qCMi ↔
      ((∃ n, EvalGraph n (CimcicTV k) MirrorV (CimcicTV k) 1) → (∃ n, EvalGraph n MirrorV (CimcicTV k) MirrorV 1)) := by
  rw [qCMi_def, eval_qCG_swap_iff_V]
  exact eval_qCTG_iff_V k _ _ _ (descT_mirror k)

/-- **The Löb family of the Mirror cell**: `pCMi := qCMi ⋏ (its transposition)`. -/
noncomputable def pCMi : Semisentence LAct 1 := pGC (cl TM) (numT 0) (numT 1)

lemma pCMi_def : pCMi = pGC (cl TM) (numT 0) (numT 1) := rfl

/-- **The bounded Löb premise of the Mirror family, slack `(7, 8)`**: a box of `pCMi(k)` makes both
searchers find their guards against Mirror, `CimcicV k` cooperates and `CimcicTV k` defects (fuel 2),
Mirror COPIES (fuel 3), so both implications are true in both readings. -/
theorem loebSound_pCMi : LoebSound pCMi 7 8 := by
  intro V _ _ k a ha h
  have : V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁ := inferInstance
  have ha' : a + 8 * (formulaLen LAct (instB (⌜qCG (cl TM) (numT 0) (numT 1)⌝ : V) k) +
      formulaLen LAct (instB (⌜qCTG (Semiterm.lMap swap (cl TM : Semiterm LAct Empty 1))
        (Semiterm.lMap swap (numT 0)) (Semiterm.lMap swap (numT 1))⌝ : V) k)) + 7 ≤ k :=
    le_trans (pConj_slack_le a _ _ _ (formulaLen_instB_pGC (cl TM) (numT 0) (numT 1) k)) ha
  obtain ⟨h1, h2⟩ := pGC_both_V k (cl TM) (numT 0) (numT 1) (hX_mirror k) hU_mirror hW_mirror a ha' h
  rw [transposeCode_MirrorV] at h2
  exact ⟨(eval_pGC_iff_stdReading k (cl TM) (numT 0) (numT 1) (desc_mirror k) (descT_mirror k)).mpr
      ⟨fun _ ↦ ⟨3, mirror_copies2_V _ _ h1⟩, fun _ ↦ ⟨3, mirror_copies2_V _ _ h2⟩⟩,
    (eval_pGC_iff_swap k (cl TM) (numT 0) (numT 1) (desc_mirror k) (descT_mirror k)).mpr
      ⟨fun _ ↦ ⟨3, mirror_copies2_V _ _ h1⟩, fun _ ↦ ⟨3, mirror_copies2_V _ _ h2⟩⟩⟩

/-- **The Mirror cell, packaged**: for all large `k`, both searchers find their guards against
Mirror (fuel 2) and both guard boxes hold. -/
theorem loeb_Cimcic_vs_Mirror_core_of_nec {d : ℕ} (hE : BoundedInnerNec d) :
    ∃ k₀ : ℕ, ∀ k : ℕ, k₀ < k →
      (EvalGraph 2 (Cimcic k) Mirror (Cimcic k) 0 ∧ EvalGraph 2 (CimcicTV (V := ℕ) k) Mirror (CimcicTV k) 1) ∧
      (LenBox TAct k (guardCode (⌜templateC⌝ : ℕ) (Cimcic k) Mirror) ∧
        LenBox TAct k (guardCode (⌜templateCT⌝ : ℕ) (CimcicTV (V := ℕ) k) Mirror)) := by
  obtain ⟨k₀, h⟩ := family_found pCMi hE loebSound_pCMi
  refine ⟨k₀, fun k hk ↦ ?_⟩
  obtain ⟨a, ha, hpc⟩ := h k hk
  have ha' := le_def.mpr (pConj_slack_nat a _ _ _ k (formulaLen_instB_pGC (V := ℕ) (cl TM) (numT 0) (numT 1) k) ha)
  have h1 := pGC_both_V (V := ℕ) k (cl TM) (numT 0) (numT 1) (hX_mirror k) hU_mirror hW_mirror a ha' hpc
  have h2 := pGC_guards_V (V := ℕ) k (cl TM) (numT 0) (numT 1) (hX_mirror k) hU_mirror hW_mirror a ha' hpc
  rw [transposeCode_MirrorV] at h1 h2
  exact ⟨h1, h2⟩

/-- **CIMCIC × Mirror is `(C, C)` in PA-`S'`, conditional on bounded inner necessitation**: for all
large `k`, `Cimcic k` cooperates with Mirror (fuel 2) and Mirror copies (fuel 3). -/
theorem loeb_Cimcic_vs_Mirror_of_nec {d : ℕ} (hE : BoundedInnerNec d) :
    ∃ k₀ : ℕ, ∀ k : ℕ, k₀ < k →
      EvalGraph 2 (Cimcic k) Mirror (Cimcic k) 0 ∧ EvalGraph 3 Mirror (Cimcic k) Mirror 0 := by
  obtain ⟨k₀, h⟩ := loeb_Cimcic_vs_Mirror_core_of_nec hE
  exact ⟨k₀, fun k hk ↦ ⟨(h k hk).1.1, mirror_copies2_V (V := ℕ) (Cimcic k) 0 (h k hk).1.1⟩⟩

/-- **The box form**: for all large `k`, CIMCIC FINDS a proof of its guard against Mirror within its
budget `k` (conditional). -/
theorem loeb_Cimcic_vs_Mirror_guard_of_nec {d : ℕ} (hE : BoundedInnerNec d) :
    ∃ k₀ : ℕ, ∀ k : ℕ, k₀ < k → LenBox TAct k (guardCode (⌜templateC⌝ : ℕ) (Cimcic k) Mirror) := by
  obtain ⟨k₀, h⟩ := loeb_Cimcic_vs_Mirror_core_of_nec hE
  exact ⟨k₀, fun k hk ↦ (h k hk).2.1⟩

/-- **CIMCIC × Mirror `(C, C)` in PA-`S'`, unconditional**: for all large `k`, `Cimcic k` cooperates
with Mirror and Mirror copies. -/
theorem loeb_Cimcic_vs_Mirror :
    ∃ k₀ : ℕ, ∀ k : ℕ, k₀ < k →
      EvalGraph 2 (Cimcic k) Mirror (Cimcic k) 0 ∧ EvalGraph 3 Mirror (Cimcic k) Mirror 0 :=
  loeb_Cimcic_vs_Mirror_of_nec boundedInnerNec_sixteen

/-- **CIMCIC finds its guard against Mirror, unconditional.** -/
theorem loeb_Cimcic_vs_Mirror_guard :
    ∃ k₀ : ℕ, ∀ k : ℕ, k₀ < k → LenBox TAct k (guardCode (⌜templateC⌝ : ℕ) (Cimcic k) Mirror) :=
  loeb_Cimcic_vs_Mirror_guard_of_nec boundedInnerNec_sixteen

end mirrorCell

/-! ### 9. Cell 3 — CIMCIC × CIMCIC `(C, C)`, NO Löb: the guard is a tautology -/

section selfCell

/-- **The fixed formula of CIMCIC against itself**: `qCC(k)` says "`CimcicV k` plays C against
itself implies `CimcicV k` plays C against itself" — the two atoms coincide. -/
noncomputable def qCC : Semisentence LAct 1 := qCG TCi uCi wCi

lemma qCC_def : qCC = qCG TCi uCi wCi := rfl

/-- **The instance equation on codes**: CIMCIC's guard code against itself is the `binNumeral k`-instance
of `⌜qCC⌝`, in every model. -/
theorem guardCode_CimcicV_self_eq_instB (k : V) :
    guardCode (⌜templateC⌝ : V) (CimcicV k) (CimcicV k) = instB (⌜qCC⌝ : V) k :=
  guardCode_CimcicV_eq_instB k TCi uCi wCi (hX_cimcic k) (hU_cimcic k) (hW_cimcic k)

/-- **The truth equation of `qCC` in every model** (standard reading): `A → A`. -/
theorem eval_qCC_iff_V (k : V) :
    Semiformula.Eval (s := stdReadingV V) ![k] Empty.elim qCC ↔
      ((∃ n, EvalGraph n (CimcicV k) (CimcicV k) (CimcicV k) 0) →
        (∃ n, EvalGraph n (CimcicV k) (CimcicV k) (CimcicV k) 0)) :=
  eval_qCG_iff_V k TCi uCi wCi (desc_cimcic k)

/-- **The truth equation of `qCC` in the swapped reading**: the transposed searcher against itself,
again `A → A`. -/
theorem eval_qCC_swap_iff_V (k : V) :
    Semiformula.Eval (s := swappedReading V) ![k] Empty.elim qCC ↔
      ((∃ n, EvalGraph n (CimcicTV k) (CimcicTV k) (CimcicTV k) 1) →
        (∃ n, EvalGraph n (CimcicTV k) (CimcicTV k) (CimcicTV k) 1)) := by
  rw [qCC_def, eval_qCG_swap_iff_V]
  exact eval_qCTG_iff_V k _ _ _ (descT_cimcic k)

/-- **`TAct ⊢ ∀ k, qCC(k)`** — the guard is a tautology in both readings (the `S'` twin of the
engine's `Pf.implRefl`), by completeness over the two standard readings. -/
theorem tact_proves_qCC : TAct ⊢ ∀¹ qCC := by
  refine TAct_complete_of_readings _ fun M _ _ ↦ ?_
  have : M↓[ℒₒᵣ] ⊧* 𝗜𝚺₁ := inferInstance
  constructor
  · simp only [Semiformula.eval_all]
    intro x
    rw [← stdReadingV_eq_stdReading]
    exact (eval_qCC_iff_V x).mpr id
  · simp only [Semiformula.eval_all]
    intro x
    exact (eval_qCC_swap_iff_V x).mpr id

/-- The tautology has a bounded proof code, of some standard length `N`, in every model (the
`exists_forward_length` pattern). -/
theorem exists_qCC_length : ∃ N : ℕ, ∀ (V : Type) [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁],
    LenBoxUnbounded TAct (N : V) (⌜(∀¹ qCC : Sentence LAct)⌝ : V) :=
  exists_lenBoxUnbounded_V_of_proof _ tact_proves_qCC

/-- **The instantiated tautology, in every model** (the `forward_inst_V` pattern): from `□_N ∀¹ qCC`,
a proof code of CIMCIC's guard against itself of length
`≤ N + 5|qCC(k)| + 3|qCC| + |binNumeral k| + 7` — LINEAR in the bit length of `k`, with no Löb step. -/
theorem qCC_inst_V {N : V} (h : LenBoxUnbounded TAct N (⌜(∀¹ qCC : Sentence LAct)⌝ : V)) (k : V) :
    LenBoxUnbounded TAct
      (N + 5 * formulaLen LAct (instB (⌜qCC⌝ : V) k) + 3 * formulaLen LAct (⌜qCC⌝ : V)
        + termLen LAct (binNumeral k) + 7)
      (guardCode (⌜templateC⌝ : V) (CimcicV k) (CimcicV k)) := by
  rw [quote_all_sentence] at h
  rw [guardCode_CimcicV_self_eq_instB]
  exact lenBoxUnbounded_instB_V (Sentence.quote_isSemiformul₁ qCC) h


/-- **CIMCIC finds its guard against itself, for all large `k`, with NO hypothesis**: at ℕ the instance
of the tautology costs `K₀ + K₁·size k` (`lenBoxNat_inst_size` + `formulaLenMeta_subst_binNumeralMeta_le`), below `k`
for all large `k` (`linear_size_le_eventually`) — `Common/Khat.found_of_all`, the generic form of this argument. -/
theorem pos_Cimcic_vs_Cimcic_guard :
    ∃ k₀ : ℕ, ∀ k : ℕ, k₀ < k → LenBox TAct k (guardCode (⌜templateC⌝ : ℕ) (Cimcic k) (Cimcic k)) := by
  exact found_of_all tact_proves_qCC _ fun k ↦ guardCode_CimcicV_self_eq_instB (V := ℕ) k

/-- **CIMCIC × CIMCIC `(C, C)` in PA-`S'`, unconditional and Löb-free**: for all large `k`,
`Cimcic k` cooperates with itself (fuel 2). -/
theorem pos_Cimcic_vs_Cimcic :
    ∃ k₀ : ℕ, ∀ k : ℕ, k₀ < k → EvalGraph 2 (Cimcic k) (Cimcic k) (Cimcic k) 0 := by
  obtain ⟨k₀, h⟩ := pos_Cimcic_vs_Cimcic_guard
  exact ⟨k₀, fun k hk ↦ cimcic_search_V (V := ℕ) k (Cimcic k) (h k hk)⟩

/-- The consulted guard of the engine's `CIMCIC k` against itself (`Agent.guardOf`) is the guard
code of `Cimcic k` on `templateC`. -/
lemma guardOf_CIMCIC (k : ℕ) :
    guardOf phiC (PD.Bots.CIMCIC k) (PD.Bots.CIMCIC k) = guardCode (⌜templateC⌝ : ℕ) (Cimcic k) (Cimcic k) := by
  unfold guardOf; rw [progCode_CIMCIC, templateCode_eq_quote_template phiC (noSelfIdxF_of_fragF _ fragF_phiC)]; rfl

/-- **The engine-facing form**: for all large `k`, the guard the arithmetized evaluator consults for
the engine's `CIMCIC k` against itself has a `TAct`-proof within the budget `k`. -/
theorem pos_CIMCIC_vs_CIMCIC_guardOf :
    ∃ k₀ : ℕ, ∀ k : ℕ, k₀ < k → LenBox TAct k (guardOf phiC (PD.Bots.CIMCIC k) (PD.Bots.CIMCIC k)) := by
  obtain ⟨k₀, h⟩ := pos_Cimcic_vs_Cimcic_guard
  exact ⟨k₀, fun k hk ↦ by rw [guardOf_CIMCIC]; exact h k hk⟩

end selfCell

end ArithS
