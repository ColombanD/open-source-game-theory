import ArithS.Cells.PositiveCells

/-!
# ArithS.Cells.CimcicEngine — CIMCIC × DupocBot `(C, C)` on the ENGINE's program codes

`Cells/CIMCIC.lean` §7 proves the mutual family CIMCIC × Dupoc `(C, C)` with Dupoc as the
hand-template twin `Dupoc k` (the searcher on `guardTemplate 0`, described by `(TD, uD, wD)`). This
file is the same cell with the engine's own code in Dupoc's place: `progCode (DupocBot k) = SV gDu 0 k`
(`progCode_DupocBot_SV`), the searcher on the TRANSLATED template `gDu = template (.plays .opp .self .C)`,
described by the generic searcher triple `(TS gDu 0, uS gDu 0, wS gDu 0)` (`Cells/Common/Bots` §4). It
retires the twin cell `outcome_CIMCIC_vs_Dupoc` in favour of `outcome_CIMCIC_vs_DupocBot`
(`Outcome/Matrix/CIMCIC.lean`); the twin theorems of `Cells/CIMCIC.lean` are untouched.

The family is the four-guard conjunction of `Cells/CIMCIC.lean` §7, verbatim in shape:
* `qCDb := qCG (TS gDu 0) (uS gDu 0) (wS gDu 0)` — CIMCIC's implication guard against `SV gDu 0 k`
  ("I play C against DupocBot ⇒ DupocBot plays C against me"), with `pGC (TS gDu 0) …` its two-sided
  family (the transposed searcher against `SV gCu 1 k = transposeCode (SV gDu 0 k)`);
* `qDbCi := qT gDu (TS gDu 0) (uS gDu 0) (wS gDu 0) TCi uCi wCi` — DupocBot's atom guard against CIMCIC
  ("CIMCIC plays C against me"), `guardCode_qT_eq_instB` in place of the hand instance
  `guardCode_GtmplA_eq_instB`; `pDbCi := qDbCi ⋏ lMap swap qDbCi`;
* `pCiDb := pGC (TS gDu 0) (uS gDu 0) (wS gDu 0) ⋏ pDbCi`.

A box of `pCiDb(k)` yields the four guard boxes by the two-level ∧-elimination (`pCiDb_all_V`, slack
`(14, 16)`: `slack4_le`/`slack4_le'`), the searchers commit at fuel 2 (`cimcic_search_V`,
`cimcicT_search_V`, `SV_search_V`), so CIMCIC's implications have true consequents and DupocBot's/
CupodBot's atoms are true, in both readings (`loebSound_pCiDb : LoebSound pCiDb 14 16`);
`family_found _ boundedInnerNec_sixteen` closes it: **`loeb_CIMCIC_vs_DupocBot`** (both cooperate at
fuel 2, on `progCode (CIMCIC k)` and `progCode (DupocBot k)`) and `loeb_CIMCIC_vs_DupocBot_guards` (both
boxes, on `templateCode phiC` / `templateCode phiDu`).

Conventions: every threshold is EXISTENTIAL; `simp` never sees a closed quote (the quote equations are for
VARIABLE sentences); `omega` is never asked about `V`; at `V = ℕ` the V-generic `≤` is bridged by `le_def`.
-/

namespace ArithS

open FFL FFL.FirstOrder Arithmetic Bootstrapping
open PeanoMinus ISigma0 ISigma1
open FFL.FirstOrder.Arithmetic.Bootstrapping.Arithmetic
open LAct
open PD.Bots

variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

/-! ### 1. The engine Dupoc and its transposition -/

section engineDupoc

/-- τ on the engine Dupoc: `transposeCode (SV gDu 0 k) = SV gCu 1 k` (the engine Cupod). -/
theorem transposeCode_SVDu (k : V) : transposeCode (SV gDu 0 k) = SV gCu 1 k := by
  have h := transposeCode_SV gDu 0 (Or.inl rfl) k
  rwa [lMap_swap_gDu] at h

/-- The engine Dupoc's triple describes `SV gDu 0 k` in `stdReadingV V`. -/
lemma desc_SVDu (k : V) :
    revalue ((uS gDu 0).val (s := stdReadingV V) ![] Empty.elim) ((wS gDu 0).val (s := stdReadingV V) ![] Empty.elim)
      ((TS gDu 0).val (s := stdReadingV V) ![k] Empty.elim) = SV gDu 0 k :=
  desc_SV gDu 0 (Or.inl rfl) k

/-- The transposed triple describes the engine Cupod `SV gCu 1 k` in `stdReadingV V`. -/
lemma descT_SVDu (k : V) :
    revalue ((Semiterm.lMap swap (uS gDu 0)).val (s := stdReadingV V) ![] Empty.elim)
      ((Semiterm.lMap swap (wS gDu 0)).val (s := stdReadingV V) ![] Empty.elim)
      ((Semiterm.lMap swap (TS gDu 0)).val (s := stdReadingV V) ![k] Empty.elim) = SV gCu 1 k := by
  have h := descT_SV gDu 0 (Or.inl rfl) k
  rwa [lMap_swap_gDu] at h

end engineDupoc

/-! ### 2. The two fixed formulas of the cell -/

section fixedFormulas

/-- **CIMCIC's guard against the engine Dupoc**: `qCDb(k)` says "`CimcicV k` plays C against `SV gDu 0 k`
implies `SV gDu 0 k` plays C against `CimcicV k`". -/
noncomputable def qCDb : Semisentence LAct 1 := qCG (TS gDu 0) (uS gDu 0) (wS gDu 0)

lemma qCDb_def : qCDb = qCG (TS gDu 0) (uS gDu 0) (wS gDu 0) := rfl

/-- **The instance equation on codes**: CIMCIC's guard code against `SV gDu 0 k`. -/
theorem guardCode_CimcicV_SVDu_eq_instB (k : V) :
    guardCode (⌜templateC⌝ : V) (CimcicV k) (SV gDu 0 k) = instB (⌜qCDb⌝ : V) k :=
  guardCode_CimcicV_eq_instB k (TS gDu 0) (uS gDu 0) (wS gDu 0) (hX_SV gDu 0 (Or.inl rfl) k)
    (hU_SV gDu 0 (Or.inl rfl) k) (hW_SV gDu 0 (Or.inl rfl) k)

/-- **The truth equation of `qCDb` in every model** (standard reading). -/
theorem eval_qCDb_iff_V (k : V) :
    Semiformula.Eval (s := stdReadingV V) ![k] Empty.elim qCDb ↔
      ((∃ n, EvalGraph n (CimcicV k) (SV gDu 0 k) (CimcicV k) 0) →
        (∃ n, EvalGraph n (SV gDu 0 k) (CimcicV k) (SV gDu 0 k) 0)) :=
  eval_qCG_iff_V k (TS gDu 0) (uS gDu 0) (wS gDu 0) (desc_SVDu k)

/-- **The truth equation of `qCDb` in the swapped reading**: the transposed searcher against the engine
Cupod, "D implies Cupod plays D". -/
theorem eval_qCDb_swap_iff_V (k : V) :
    Semiformula.Eval (s := swappedReading V) ![k] Empty.elim qCDb ↔
      ((∃ n, EvalGraph n (CimcicTV k) (SV gCu 1 k) (CimcicTV k) 1) →
        (∃ n, EvalGraph n (SV gCu 1 k) (CimcicTV k) (SV gCu 1 k) 1)) := by
  rw [qCDb_def, eval_qCG_swap_iff_V]
  exact eval_qCTG_iff_V k _ _ _ (descT_SVDu k)

/-- **The engine Dupoc's guard against CIMCIC**: `qDbCi(k)` says "`CimcicV k` plays C against
`SV gDu 0 k`" — the translated template `gDu` filled with Dupoc's triple (me) and CIMCIC's triple (opp). -/
noncomputable def qDbCi : Semisentence LAct 1 := qT gDu (TS gDu 0) (uS gDu 0) (wS gDu 0) TCi uCi wCi

lemma qDbCi_def : qDbCi = qT gDu (TS gDu 0) (uS gDu 0) (wS gDu 0) TCi uCi wCi := rfl

/-- **The instance equation on codes**: the engine Dupoc's guard code against `CimcicV k`. -/
theorem guardCode_SVDu_CimcicV_eq_instB (k : V) :
    guardCode (⌜gDu⌝ : V) (SV gDu 0 k) (CimcicV k) = instB (⌜qDbCi⌝ : V) k :=
  guardCode_qT_eq_instB gDu k _ _ _ _ _ _ (hX_SV gDu 0 (Or.inl rfl) k) (hU_SV gDu 0 (Or.inl rfl) k)
    (hW_SV gDu 0 (Or.inl rfl) k) (hX_cimcic k) (hU_cimcic k) (hW_cimcic k)

/-- **The transposed instance equation**: the engine Cupod's guard code against `CimcicTV k` is the
`binNumeral k`-instance of `⌜lMap swap qDbCi⌝`. -/
theorem guardCode_SVCu_CimcicTV_eq_instB (k : V) :
    guardCode (⌜gCu⌝ : V) (SV gCu 1 k) (CimcicTV k) = instB (⌜Semiformula.lMap swap qDbCi⌝ : V) k := by
  have h := guardCode_qT_swap_eq_instB gDu k _ _ _ _ _ _ (hX_SV gDu 0 (Or.inl rfl) k) (hU_SV gDu 0 (Or.inl rfl) k)
    (hW_SV gDu 0 (Or.inl rfl) k) (hX_cimcic k) (hU_cimcic k) (hW_cimcic k)
  rwa [transposeCode_SVDu, lMap_swap_gDu, transposeCode_CimcicV] at h

/-- **The truth equation of `qDbCi` in every model** (standard reading). -/
theorem eval_qDbCi_iff_V (k : V) :
    Semiformula.Eval (s := stdReadingV V) ![k] Empty.elim qDbCi ↔
      ∃ n, EvalGraph n (CimcicV k) (SV gDu 0 k) (CimcicV k) 0 := by
  rw [qDbCi_def, eval_qT_plays_opp_self .C _ _ _ _ _ _ k (desc_SVDu k) (desc_cimcic k), actCode_C_cast]

/-- **The truth equation of `lMap swap qDbCi` in every model** (standard reading): "`CimcicTV k` plays
D against the engine Cupod `SV gCu 1 k`". -/
theorem eval_qDbCi_swapped_iff_V (k : V) :
    Semiformula.Eval (s := stdReadingV V) ![k] Empty.elim (Semiformula.lMap swap qDbCi) ↔
      ∃ n, EvalGraph n (CimcicTV k) (SV gCu 1 k) (CimcicTV k) 1 := by
  rw [qDbCi_def, lMap_swap_qT, lMap_swap_gDu,
    eval_qT_plays_opp_self .D _ _ _ _ _ _ k (descT_SVDu k) (descT_cimcic k), actCode_D_cast]

end fixedFormulas

/-! ### 3. The mutual family -/

section family

/-- The two-sided conjunct of the mutual family: the engine Dupoc's guard against CIMCIC and its
transposition. -/
noncomputable def pDbCi : Semisentence LAct 1 := qDbCi ⋏ Semiformula.lMap swap qDbCi

lemma pDbCi_def : pDbCi = qDbCi ⋏ Semiformula.lMap swap qDbCi := rfl

lemma lMap_swap_pDbCi : Semiformula.lMap swap pDbCi = Semiformula.lMap swap qDbCi ⋏ qDbCi := by
  rw [pDbCi_def, LogicalConnective.HomClass.map_and, lMap_swap_swap]

/-- **The MUTUAL Löb family of the CIMCIC × DupocBot cell**: CIMCIC's family against the engine Dupoc's
triple (and the transposed searcher's against the engine Cupod's) AND the engine Dupoc's guard against
CIMCIC (and its transposition) — four guards, each searcher's box supplied by the same conjunction. -/
noncomputable def pCiDb : Semisentence LAct 1 := pGC (TS gDu 0) (uS gDu 0) (wS gDu 0) ⋏ pDbCi

lemma pCiDb_def : pCiDb = pGC (TS gDu 0) (uS gDu 0) (wS gDu 0) ⋏ pDbCi := rfl

theorem instB_quote_pDbCi (k : V) :
    instB (⌜pDbCi⌝ : V) k = instB (⌜qDbCi⌝ : V) k ^⋏ instB (⌜Semiformula.lMap swap qDbCi⌝ : V) k :=
  instB_quote_and _ _ k

theorem instB_quote_pCiDb (k : V) :
    instB (⌜pCiDb⌝ : V) k = instB (⌜pGC (TS gDu 0) (uS gDu 0) (wS gDu 0)⌝ : V) k ^⋏ instB (⌜pDbCi⌝ : V) k :=
  instB_quote_and _ _ k

lemma formulaLen_instB_pDbCi (k : V) :
    formulaLen LAct (instB (⌜pDbCi⌝ : V) k) =
      formulaLen LAct (instB (⌜qDbCi⌝ : V) k) + formulaLen LAct (instB (⌜Semiformula.lMap swap qDbCi⌝ : V) k) + 1 := by
  rw [instB_quote_pDbCi,
    formulaLen_and (isFormula_instB_quote _ k).isUFormula (isFormula_instB_quote _ k).isUFormula]

lemma formulaLen_instB_pCiDb (k : V) :
    formulaLen LAct (instB (⌜pCiDb⌝ : V) k) =
      formulaLen LAct (instB (⌜pGC (TS gDu 0) (uS gDu 0) (wS gDu 0)⌝ : V) k) + formulaLen LAct (instB (⌜pDbCi⌝ : V) k) + 1 := by
  rw [instB_quote_pCiDb,
    formulaLen_and (isFormula_instB_quote _ k).isUFormula (isFormula_instB_quote _ k).isUFormula]

/-- **All four searchers find their guards from a box of the mutual family** (fuel 2): CIMCIC cooperates
with the engine Dupoc, the transposed searcher defects against the engine Cupod, the engine Dupoc
cooperates with CIMCIC, the engine Cupod defects against the transposed searcher. -/
theorem pCiDb_all_V (k a : V)
    (ha₁ : a + 8 * (formulaLen LAct (instB (⌜pGC (TS gDu 0) (uS gDu 0) (wS gDu 0)⌝ : V) k) +
        formulaLen LAct (instB (⌜pDbCi⌝ : V) k)) + 7 +
      8 * (formulaLen LAct (instB (⌜qCG (TS gDu 0) (uS gDu 0) (wS gDu 0)⌝ : V) k) +
        formulaLen LAct (instB (⌜qCTG (Semiterm.lMap swap (TS gDu 0)) (Semiterm.lMap swap (uS gDu 0))
          (Semiterm.lMap swap (wS gDu 0))⌝ : V) k))
      + 7 ≤ k)
    (ha₂ : a + 8 * (formulaLen LAct (instB (⌜pGC (TS gDu 0) (uS gDu 0) (wS gDu 0)⌝ : V) k) +
        formulaLen LAct (instB (⌜pDbCi⌝ : V) k)) + 7 +
      8 * (formulaLen LAct (instB (⌜qDbCi⌝ : V) k) + formulaLen LAct (instB (⌜Semiformula.lMap swap qDbCi⌝ : V) k))
      + 7 ≤ k)
    (h : LenBoxUnbounded TAct a (instB (⌜pCiDb⌝ : V) k)) :
    (EvalGraph 2 (CimcicV k) (SV gDu 0 k) (CimcicV k) 0 ∧ EvalGraph 2 (CimcicTV k) (SV gCu 1 k) (CimcicTV k) 1) ∧
    (EvalGraph 2 (SV gDu 0 k) (CimcicV k) (SV gDu 0 k) 0 ∧ EvalGraph 2 (SV gCu 1 k) (CimcicTV k) (SV gCu 1 k) 1) := by
  rw [instB_quote_pCiDb] at h
  have hx := isFormula_instB_quote (pGC (TS gDu 0) (uS gDu 0) (wS gDu 0)) k
  have hy := isFormula_instB_quote pDbCi k
  have h₁ := lenBoxUnbounded_andL_V hx hy h
  have h₂ := lenBoxUnbounded_andR_V hx hy h
  obtain ⟨g1, g2⟩ := pGC_both_V k (TS gDu 0) (uS gDu 0) (wS gDu 0) (hX_SV gDu 0 (Or.inl rfl) k)
    (hU_SV gDu 0 (Or.inl rfl) k) (hW_SV gDu 0 (Or.inl rfl) k) _ ha₁ h₁
  rw [transposeCode_SVDu] at g2
  have hx' := isFormula_instB_quote qDbCi k
  have hy' := isFormula_instB_quote (Semiformula.lMap swap qDbCi) k
  have h₂' : LenBoxUnbounded TAct
      (a + 8 * (formulaLen LAct (instB (⌜pGC (TS gDu 0) (uS gDu 0) (wS gDu 0)⌝ : V) k) +
        formulaLen LAct (instB (⌜pDbCi⌝ : V) k)) + 7)
      (instB (⌜qDbCi⌝ : V) k ^⋏ instB (⌜Semiformula.lMap swap qDbCi⌝ : V) k) := by
    rw [← instB_quote_pDbCi]; exact h₂
  have c1 := lenBoxUnbounded_mono_V ha₂ (lenBoxUnbounded_andL_V hx' hy' h₂')
  have c2 := lenBoxUnbounded_mono_V ha₂ (lenBoxUnbounded_andR_V hx' hy' h₂')
  rw [lenBoxUnbounded_iff_lenBox, ← guardCode_SVDu_CimcicV_eq_instB] at c1
  rw [lenBoxUnbounded_iff_lenBox, ← guardCode_SVCu_CimcicTV_eq_instB] at c2
  have e1 := SV_search_V gDu 0 k (CimcicV k) c1
  have e2 := SV_search_V gCu 1 k (CimcicTV k) c2
  rw [Nat.cast_zero] at e1
  rw [Nat.cast_one] at e2
  exact ⟨⟨g1, g2⟩, ⟨e1, e2⟩⟩

/-- **The box form**: the two guards of the cell are provable within `k`. -/
theorem pCiDb_guards_V (k a : V)
    (ha₁ : a + 8 * (formulaLen LAct (instB (⌜pGC (TS gDu 0) (uS gDu 0) (wS gDu 0)⌝ : V) k) +
        formulaLen LAct (instB (⌜pDbCi⌝ : V) k)) + 7 +
      8 * (formulaLen LAct (instB (⌜qCG (TS gDu 0) (uS gDu 0) (wS gDu 0)⌝ : V) k) +
        formulaLen LAct (instB (⌜qCTG (Semiterm.lMap swap (TS gDu 0)) (Semiterm.lMap swap (uS gDu 0))
          (Semiterm.lMap swap (wS gDu 0))⌝ : V) k))
      + 7 ≤ k)
    (ha₂ : a + 8 * (formulaLen LAct (instB (⌜pGC (TS gDu 0) (uS gDu 0) (wS gDu 0)⌝ : V) k) +
        formulaLen LAct (instB (⌜pDbCi⌝ : V) k)) + 7 +
      8 * (formulaLen LAct (instB (⌜qDbCi⌝ : V) k) + formulaLen LAct (instB (⌜Semiformula.lMap swap qDbCi⌝ : V) k))
      + 7 ≤ k)
    (h : LenBoxUnbounded TAct a (instB (⌜pCiDb⌝ : V) k)) :
    LenBox TAct k (guardCode (⌜templateC⌝ : V) (CimcicV k) (SV gDu 0 k)) ∧
    LenBox TAct k (guardCode (⌜gDu⌝ : V) (SV gDu 0 k) (CimcicV k)) := by
  rw [instB_quote_pCiDb] at h
  have hx := isFormula_instB_quote (pGC (TS gDu 0) (uS gDu 0) (wS gDu 0)) k
  have hy := isFormula_instB_quote pDbCi k
  have h₁ := lenBoxUnbounded_andL_V hx hy h
  have h₂ := lenBoxUnbounded_andR_V hx hy h
  obtain ⟨g1, _⟩ := pGC_guards_V k (TS gDu 0) (uS gDu 0) (wS gDu 0) (hX_SV gDu 0 (Or.inl rfl) k)
    (hU_SV gDu 0 (Or.inl rfl) k) (hW_SV gDu 0 (Or.inl rfl) k) _ ha₁ h₁
  have hx' := isFormula_instB_quote qDbCi k
  have hy' := isFormula_instB_quote (Semiformula.lMap swap qDbCi) k
  have h₂' : LenBoxUnbounded TAct
      (a + 8 * (formulaLen LAct (instB (⌜pGC (TS gDu 0) (uS gDu 0) (wS gDu 0)⌝ : V) k) +
        formulaLen LAct (instB (⌜pDbCi⌝ : V) k)) + 7)
      (instB (⌜qDbCi⌝ : V) k ^⋏ instB (⌜Semiformula.lMap swap qDbCi⌝ : V) k) := by
    rw [← instB_quote_pDbCi]; exact h₂
  have c1 := lenBoxUnbounded_mono_V ha₂ (lenBoxUnbounded_andL_V hx' hy' h₂')
  rw [lenBoxUnbounded_iff_lenBox, ← guardCode_SVDu_CimcicV_eq_instB] at c1
  exact ⟨g1, c1⟩

/-! #### `pCiDb` in both readings -/

/-- `pCiDb(k)` in the standard reading. -/
theorem eval_pCiDb_iff_std (k : V) :
    Semiformula.Eval (s := stdReadingV V) ![k] Empty.elim pCiDb ↔
      (((∃ n, EvalGraph n (CimcicV k) (SV gDu 0 k) (CimcicV k) 0) → (∃ n, EvalGraph n (SV gDu 0 k) (CimcicV k) (SV gDu 0 k) 0)) ∧
       ((∃ n, EvalGraph n (CimcicTV k) (SV gCu 1 k) (CimcicTV k) 1) → (∃ n, EvalGraph n (SV gCu 1 k) (CimcicTV k) (SV gCu 1 k) 1))) ∧
      ((∃ n, EvalGraph n (CimcicV k) (SV gDu 0 k) (CimcicV k) 0) ∧ (∃ n, EvalGraph n (CimcicTV k) (SV gCu 1 k) (CimcicTV k) 1)) := by
  rw [pCiDb_def, pDbCi_def]
  simp only [LogicalConnective.HomClass.map_and, LogicalConnective.Prop.and_eq]
  rw [eval_pGC_iff_std k (TS gDu 0) (uS gDu 0) (wS gDu 0) (desc_SVDu k) (descT_SVDu k), eval_qDbCi_iff_V,
    eval_qDbCi_swapped_iff_V]

/-- `pCiDb(k)` in the swapped reading: the SAME content (the conjuncts exchange roles). -/
theorem eval_pCiDb_iff_swap (k : V) :
    Semiformula.Eval (s := swappedReading V) ![k] Empty.elim pCiDb ↔
      (((∃ n, EvalGraph n (CimcicV k) (SV gDu 0 k) (CimcicV k) 0) → (∃ n, EvalGraph n (SV gDu 0 k) (CimcicV k) (SV gDu 0 k) 0)) ∧
       ((∃ n, EvalGraph n (CimcicTV k) (SV gCu 1 k) (CimcicTV k) 1) → (∃ n, EvalGraph n (SV gCu 1 k) (CimcicTV k) (SV gCu 1 k) 1))) ∧
      ((∃ n, EvalGraph n (CimcicV k) (SV gDu 0 k) (CimcicV k) 0) ∧ (∃ n, EvalGraph n (CimcicTV k) (SV gCu 1 k) (CimcicTV k) 1)) := by
  rw [eval_swappedReading, pCiDb_def, LogicalConnective.HomClass.map_and, lMap_swap_pGC, lMap_swap_pDbCi,
    ← stdReadingV_eq_stdReading]
  simp only [LogicalConnective.HomClass.map_and, LogicalConnective.Prop.and_eq]
  rw [eval_qCG_iff_V k (TS gDu 0) (uS gDu 0) (wS gDu 0) (desc_SVDu k), eval_qCTG_iff_V k _ _ _ (descT_SVDu k),
    eval_qDbCi_iff_V, eval_qDbCi_swapped_iff_V,
    and_comm (a := ∃ n, EvalGraph n (CimcicTV k) (SV gCu 1 k) (CimcicTV k) 1),
    and_comm (a := (∃ n, EvalGraph n (CimcicTV k) (SV gCu 1 k) (CimcicTV k) 1) → _)]

theorem eval_pCiDb_iff_stdReading (k : V) :
    Semiformula.Eval (s := stdReading V) ![k] Empty.elim pCiDb ↔
      (((∃ n, EvalGraph n (CimcicV k) (SV gDu 0 k) (CimcicV k) 0) → (∃ n, EvalGraph n (SV gDu 0 k) (CimcicV k) (SV gDu 0 k) 0)) ∧
       ((∃ n, EvalGraph n (CimcicTV k) (SV gCu 1 k) (CimcicTV k) 1) → (∃ n, EvalGraph n (SV gCu 1 k) (CimcicTV k) (SV gCu 1 k) 1))) ∧
      ((∃ n, EvalGraph n (CimcicV k) (SV gDu 0 k) (CimcicV k) 0) ∧ (∃ n, EvalGraph n (CimcicTV k) (SV gCu 1 k) (CimcicTV k) 1)) := by
  rw [← stdReadingV_eq_stdReading]; exact eval_pCiDb_iff_std k

/-- **The bounded Löb premise of the mutual family, slack `(14, 16)`**: a box of `pCiDb(k)` makes all four
searchers find their guards (fuel 2); CIMCIC's implications hold because the engine Dupoc/Cupod actually
play the consequents, and their guards are the plays of CIMCIC/its transposition — true in both readings. -/
theorem loebSound_pCiDb : LoebSound pCiDb 14 16 := by
  intro V _ _ k a ha h
  have : V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁ := inferInstance
  have ha₁ := le_trans (slack4_le a _ _ _ _ _ (formulaLen_instB_pGC (TS gDu 0) (uS gDu 0) (wS gDu 0) k)
    (formulaLen_instB_pCiDb k)) ha
  have ha₂ := le_trans (slack4_le' a _ _ _ _ _ (formulaLen_instB_pDbCi k) (formulaLen_instB_pCiDb k)) ha
  obtain ⟨⟨g1, g2⟩, ⟨c1, c2⟩⟩ := pCiDb_all_V k a ha₁ ha₂ h
  exact ⟨(eval_pCiDb_iff_stdReading k).mpr ⟨⟨fun _ ↦ ⟨2, c1⟩, fun _ ↦ ⟨2, c2⟩⟩, ⟨⟨2, g1⟩, ⟨2, g2⟩⟩⟩,
    (eval_pCiDb_iff_swap k).mpr ⟨⟨fun _ ↦ ⟨2, c1⟩, fun _ ↦ ⟨2, c2⟩⟩, ⟨⟨2, g1⟩, ⟨2, g2⟩⟩⟩⟩

end family

/-! ### 4. The cell -/

section cell

/-- **The CIMCIC × DupocBot cell at ℕ, packaged**: for all large `k`, CIMCIC cooperates with the engine
Dupoc and the engine Dupoc cooperates with CIMCIC (fuel 2), and both guard boxes hold. -/
theorem loeb_CIMCIC_vs_DupocBot_core_of_nec {d : ℕ} (hE : BoundedInnerNec d) :
    ∃ k₀ : ℕ, ∀ k : ℕ, k₀ < k →
      (EvalGraph 2 (Cimcic k) (SV (V := ℕ) gDu 0 k) (Cimcic k) 0 ∧
        EvalGraph 2 (SV (V := ℕ) gDu 0 k) (Cimcic k) (SV (V := ℕ) gDu 0 k) 0) ∧
      (LenBox TAct k (guardCode (⌜templateC⌝ : ℕ) (Cimcic k) (SV (V := ℕ) gDu 0 k)) ∧
        LenBox TAct k (guardCode (⌜gDu⌝ : ℕ) (SV (V := ℕ) gDu 0 k) (Cimcic k))) := by
  obtain ⟨k₀, h⟩ := family_found pCiDb hE loebSound_pCiDb
  refine ⟨k₀, fun k hk ↦ ?_⟩
  obtain ⟨a, ha, hpc⟩ := h k hk
  have ha₁ := le_def.mpr (slack4_nat a _ _ _ _ _ k
    (formulaLen_instB_pGC (V := ℕ) (TS gDu 0) (uS gDu 0) (wS gDu 0) k) (formulaLen_instB_pCiDb (V := ℕ) k) ha)
  have ha₂ := le_def.mpr (slack4_nat' a _ _ _ _ _ k (formulaLen_instB_pDbCi (V := ℕ) k)
    (formulaLen_instB_pCiDb (V := ℕ) k) ha)
  obtain ⟨⟨g1, _⟩, ⟨c1, _⟩⟩ := pCiDb_all_V (V := ℕ) k a ha₁ ha₂ hpc
  exact ⟨⟨g1, c1⟩, pCiDb_guards_V (V := ℕ) k a ha₁ ha₂ hpc⟩

/-- **CIMCIC × DupocBot is `(C, C)` in PA-`S'`, on the engine's codes, unconditional**: for all large `k`,
`progCode (CIMCIC k)` cooperates with `progCode (DupocBot k)` and conversely (fuel 2). -/
theorem loeb_CIMCIC_vs_DupocBot :
    ∃ k₀ : ℕ, ∀ k : ℕ, k₀ < k →
      EvalGraph 2 (progCode (CIMCIC k)) (progCode (DupocBot k)) (progCode (CIMCIC k)) (actCode .C) ∧
      EvalGraph 2 (progCode (DupocBot k)) (progCode (CIMCIC k)) (progCode (DupocBot k)) (actCode .C) := by
  obtain ⟨k₀, h⟩ := loeb_CIMCIC_vs_DupocBot_core_of_nec boundedInnerNec_sixteen
  exact ⟨k₀, fun k hk ↦ by rw [progCode_CIMCIC, progCode_DupocBot_SV]; exact (h k hk).1⟩

/-- **The box form, on the engine's codes**: for all large `k`, both `CIMCIC k` and `DupocBot k` FIND their
guards against each other within the budget `k`. -/
theorem loeb_CIMCIC_vs_DupocBot_guards :
    ∃ k₀ : ℕ, ∀ k : ℕ, k₀ < k →
      LenBox TAct k (guardCode (templateCode phiC) (progCode (CIMCIC k)) (progCode (DupocBot k))) ∧
      LenBox TAct k (guardCode (templateCode phiDu) (progCode (DupocBot k)) (progCode (CIMCIC k))) := by
  obtain ⟨k₀, h⟩ := loeb_CIMCIC_vs_DupocBot_core_of_nec boundedInnerNec_sixteen
  exact ⟨k₀, fun k hk ↦ by rw [progCode_CIMCIC, progCode_DupocBot_SV]; exact (h k hk).2⟩

end cell

end ArithS
