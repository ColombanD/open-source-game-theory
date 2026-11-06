import ArithS.Cells.FlipCells

/-!
# ArithS.Cells.DimcidEngine — DIMCID × CupodBot `(D, D)` on the ENGINE's codes

`Cells/DIMCID.lean` §9 proves the mutual cell DIMCID × Cupod `(D, D)` with Cupod as the hand-template
twin `Cupod k` (stored template `guardTemplate 1`, description triple `(TD, uC, wC)`). This module
re-proves the SAME cell with the engine's own opponent, `progCode (CupodBot k) = SV gCu 1 k`
(`progCode_CupodBot_SV`: the generic searcher on the translated template
`gCu = template (.plays .opp .self .D)`, then-branch `D`), and thereby RETIRES the twin-named cell
`outcome_DIMCID_vs_Cupod` in favour of `outcome_DIMCID_vs_CupodBot` (`Outcome/Matrix/DIMCID.lean`).
The hand-twin theorems of `Cells/DIMCID.lean` §9 stay as they are.

The mathematics is §9's, with the three Cupod-side ingredients swapped for their `SV` versions:

1. **Cupod's description** is the `SV` layer's canonical triple `(TS gCu 1, uS gCu 1, wS gCu 1)`
   (`Cells/Common/Bots.lean` §4: `hX/hU/hW_SV`, `desc_SV`, `descT_SV`); its transposition describes
   `SV gDu 0 k`, the engine's `DupocBot k` (`transposeCode_SV` + `lMap_swap_gCu`).
2. **Cupod's guard against DIMCID** is the generic template instance `qCDE := qT gCu (TS gCu 1)
   (uS gCu 1) (wS gCu 1) TDi uDi wDi` ("DIMCID plays D against me"): the instance equations on codes
   `guardCode_cupodE_DimcidV_eq_instB` / `guardCode_dupocE_DimcidTV_eq_instB` (`guardCode_qT_eq_instB`,
   `guardCode_qT_swap_eq_instB`) and the truth equations `eval_qCDE_iff_V` / `eval_qCDE_swapped_iff_V`
   (`eval_qT_plays_opp_self`).
3. **The search clauses** are `SV_search_V` (`Cells/Common/Probers.lean`) in place of
   `cupod_search_any_V` / `dupoc_search_any_V`.

DIMCID's side — `DimcidV`, its triple `(TDi, uDi, wDi)`, the fixed formulas `qDG`/`qTG`, the family
`pG`, the search clauses and the truth equations — is `Cells/DIMCID.lean`, reused verbatim.

**The mutual family** `pDCE := pG (TS gCu 1) (uS gCu 1) (wS gCu 1) ⋏ (qCDE ⋏ τ qCDE)` (four guards). A box
of `pDCE(k)` yields the four guard boxes by a two-level ∧-elimination (`pDCE_all_V`, slack `(14, 16)`:
`slack4_le`/`slack4_nat` of `Cells/DIMCID.lean`), so all four searchers commit at fuel 2 — DIMCID defects
against `SV gCu 1 k`, the transposed searcher cooperates with `SV gDu 0 k`, `SV gCu 1 k` defects against
DIMCID, `SV gDu 0 k` cooperates with the transposed searcher — which makes every conjunct true in both
readings (`loebSound_pDCE : LoebSound pDCE 14 16`). Then `family_found _ boundedInnerNec_sixteen`
(`Assembly/Family.lean`, `Necessitation/Package.lean`) gives, unconditionally:

* **`loeb_DIMCID_vs_CupodBot`**: for all large `k`, `progCode (DIMCID k)` defects against
  `progCode (CupodBot k)` and `progCode (CupodBot k)` defects against `progCode (DIMCID k)` (fuel 2);
* **`loeb_DIMCID_vs_CupodBot_guards`**: the box form — both guards (`templateCode phiD`,
  `templateCode phiCu`) are `TAct`-provable within `k`.

Conventions (`docs/notes/ARITH_TRAPS.md`): every threshold EXISTENTIAL; `simp` never sees a closed
quote (the quote equations are for VARIABLE sentences, instantiated; `rfl`-bridges); `omega` is never
asked about `V`; at `V = ℕ` the V-generic `≤` is bridged by `le_def`.
-/

set_option linter.constructorNameAsVariable false

namespace ArithS

open FFL FFL.FirstOrder Arithmetic Bootstrapping
open PeanoMinus ISigma0 ISigma1
open FFL.FirstOrder.Arithmetic.Bootstrapping.Arithmetic
open LAct
open PD.Bots

variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

/-! ### 1. The engine's Cupod, described by the `SV` layer -/

section cupodDesc

/-- The `X`-hypothesis: the tower `TS gCu 1` describes `SV gCu 1 k` on codes. -/
lemma hX_cupodE (k : V) :
    termSubst LAct (binNumeral k ∷ (0 : V)) (⌜(Rew.emb (TS gCu 1) : SyntacticSemiterm LAct 1)⌝ : V) =
      codeTerm (canonical (SV gCu 1 k)) :=
  hX_SV gCu 1 (Or.inr rfl) k

lemma hU_cupodE (k : V) : (⌜uS gCu 1⌝ : V) = revalueU (SV gCu 1 k) := hU_SV gCu 1 (Or.inr rfl) k
lemma hW_cupodE (k : V) : (⌜wS gCu 1⌝ : V) = revalueW (SV gCu 1 k) := hW_SV gCu 1 (Or.inr rfl) k

/-- The triple describes `SV gCu 1 k` in `stdReadingV V`. -/
lemma desc_cupodE (k : V) :
    revalue ((uS gCu 1).val (s := stdReadingV V) ![] Empty.elim) ((wS gCu 1).val (s := stdReadingV V) ![] Empty.elim)
      ((TS gCu 1).val (s := stdReadingV V) ![k] Empty.elim) = SV gCu 1 k :=
  desc_SV gCu 1 (Or.inr rfl) k

/-- The transposed triple describes the engine's Dupoc `SV gDu 0 k` in `stdReadingV V`. -/
lemma descT_cupodE (k : V) :
    revalue ((Semiterm.lMap swap (uS gCu 1)).val (s := stdReadingV V) ![] Empty.elim)
      ((Semiterm.lMap swap (wS gCu 1)).val (s := stdReadingV V) ![] Empty.elim)
      ((Semiterm.lMap swap (TS gCu 1)).val (s := stdReadingV V) ![k] Empty.elim) = SV gDu 0 k := by
  have h := descT_SV gCu 1 (Or.inr rfl) k
  rwa [lMap_swap_gCu] at h

/-- τ of the engine's Cupod is the engine's Dupoc. -/
lemma transposeCode_cupodE (k : V) : transposeCode (SV gCu 1 k) = SV gDu 0 k := by
  rw [transposeCode_SV gCu 1 (Or.inr rfl), lMap_swap_gCu]

end cupodDesc

/-! ### 2. Cupod's guard against DIMCID on the engine's template, and its transposition -/

section cupodGuard

/-- **Cupod's guard against DIMCID** on the engine's template: `qCDE(k)` says "`DimcidV k` plays D
against `SV gCu 1 k`". -/
noncomputable def qCDE : Semisentence LAct 1 := qT gCu (TS gCu 1) (uS gCu 1) (wS gCu 1) TDi uDi wDi

lemma qCDE_def : qCDE = qT gCu (TS gCu 1) (uS gCu 1) (wS gCu 1) TDi uDi wDi := rfl

lemma lMap_swap_qCDE :
    Semiformula.lMap swap qCDE =
      qT gDu (Semiterm.lMap swap (TS gCu 1)) (Semiterm.lMap swap (uS gCu 1)) (Semiterm.lMap swap (wS gCu 1))
        (Semiterm.lMap swap TDi) (Semiterm.lMap swap uDi) (Semiterm.lMap swap wDi) := by
  rw [qCDE_def, lMap_swap_qT, lMap_swap_gCu]

/-- **The instance equation on codes**: the engine Cupod's guard code against `DimcidV k`. -/
theorem guardCode_cupodE_DimcidV_eq_instB (k : V) :
    guardCode (⌜gCu⌝ : V) (SV gCu 1 k) (DimcidV k) = instB (⌜qCDE⌝ : V) k :=
  guardCode_qT_eq_instB gCu k _ _ _ _ _ _ (hX_cupodE k) (hU_cupodE k) (hW_cupodE k)
    (hX_dimcid k) (hU_dimcid k) (hW_dimcid k)

/-- **The transposed instance equation**: the engine Dupoc's guard code against `DimcidTV k` is the
`binNumeral k`-instance of `⌜lMap swap qCDE⌝`. -/
theorem guardCode_dupocE_DimcidTV_eq_instB (k : V) :
    guardCode (⌜gDu⌝ : V) (SV gDu 0 k) (DimcidTV k) = instB (⌜Semiformula.lMap swap qCDE⌝ : V) k := by
  have h := guardCode_qT_swap_eq_instB gCu k _ _ _ _ _ _ (hX_cupodE k) (hU_cupodE k) (hW_cupodE k)
    (hX_dimcid k) (hU_dimcid k) (hW_dimcid k)
  rwa [transposeCode_cupodE, lMap_swap_gCu, transposeCode_DimcidV] at h

/-- **The truth equation of `qCDE` in every model** (standard reading). -/
theorem eval_qCDE_iff_V (k : V) :
    Semiformula.Eval (s := stdReadingV V) ![k] Empty.elim qCDE ↔
      ∃ n, EvalGraph n (DimcidV k) (SV gCu 1 k) (DimcidV k) 1 := by
  rw [qCDE_def, eval_qT_plays_opp_self .D _ _ _ _ _ _ k (desc_cupodE k) (desc_dimcid k), actCode_D_cast]

/-- **The truth equation of `lMap swap qCDE` in every model** (standard reading): "`DimcidTV k` plays C
against `SV gDu 0 k`". -/
theorem eval_qCDE_swapped_iff_V (k : V) :
    Semiformula.Eval (s := stdReadingV V) ![k] Empty.elim (Semiformula.lMap swap qCDE) ↔
      ∃ n, EvalGraph n (DimcidTV k) (SV gDu 0 k) (DimcidTV k) 0 := by
  rw [lMap_swap_qCDE, eval_qT_plays_opp_self .C _ _ _ _ _ _ k (descT_cupodE k) (descT_dimcid k), actCode_C_cast]

end cupodGuard

/-! ### 3. The mutual family and its ∧-eliminations -/

section family

/-- The two-sided conjunct: the engine Cupod's guard against DIMCID and its transposition. -/
noncomputable def pCDE : Semisentence LAct 1 := qCDE ⋏ Semiformula.lMap swap qCDE

lemma pCDE_def : pCDE = qCDE ⋏ Semiformula.lMap swap qCDE := rfl

lemma lMap_swap_pCDE : Semiformula.lMap swap pCDE = Semiformula.lMap swap qCDE ⋏ qCDE := by
  rw [pCDE_def, LogicalConnective.HomClass.map_and, lMap_swap_swap]

/-- **The MUTUAL Löb family of the DIMCID × CupodBot cell**: DIMCID's family against the engine Cupod's
triple (and the transposed searcher's against the engine Dupoc's) AND Cupod's guard against DIMCID (and
its transposition) — four guards. -/
noncomputable def pDCE : Semisentence LAct 1 := pG (TS gCu 1) (uS gCu 1) (wS gCu 1) ⋏ pCDE

lemma pDCE_def : pDCE = pG (TS gCu 1) (uS gCu 1) (wS gCu 1) ⋏ pCDE := rfl

theorem instB_quote_pCDE (k : V) :
    instB (⌜pCDE⌝ : V) k = instB (⌜qCDE⌝ : V) k ^⋏ instB (⌜Semiformula.lMap swap qCDE⌝ : V) k :=
  instB_quote_and _ _ k

theorem instB_quote_pDCE (k : V) :
    instB (⌜pDCE⌝ : V) k = instB (⌜pG (TS gCu 1) (uS gCu 1) (wS gCu 1)⌝ : V) k ^⋏ instB (⌜pCDE⌝ : V) k :=
  instB_quote_and _ _ k

lemma formulaLen_instB_pCDE (k : V) :
    formulaLen LAct (instB (⌜pCDE⌝ : V) k) =
      formulaLen LAct (instB (⌜qCDE⌝ : V) k) + formulaLen LAct (instB (⌜Semiformula.lMap swap qCDE⌝ : V) k) + 1 := by
  rw [instB_quote_pCDE,
    formulaLen_and (isFormula_instB_quote _ k).isUFormula (isFormula_instB_quote _ k).isUFormula]

lemma formulaLen_instB_pDCE (k : V) :
    formulaLen LAct (instB (⌜pDCE⌝ : V) k) =
      formulaLen LAct (instB (⌜pG (TS gCu 1) (uS gCu 1) (wS gCu 1)⌝ : V) k) + formulaLen LAct (instB (⌜pCDE⌝ : V) k) + 1 := by
  rw [instB_quote_pDCE,
    formulaLen_and (isFormula_instB_quote _ k).isUFormula (isFormula_instB_quote _ k).isUFormula]

/-- **All four searchers find their guards from a box of the mutual family** (fuel 2): DIMCID defects
against the engine Cupod, the transposed searcher cooperates with the engine Dupoc, the engine Cupod
defects against DIMCID, the engine Dupoc cooperates with the transposed searcher. -/
theorem pDCE_all_V (k a : V)
    (ha₁ : a + 8 * (formulaLen LAct (instB (⌜pG (TS gCu 1) (uS gCu 1) (wS gCu 1)⌝ : V) k) + formulaLen LAct (instB (⌜pCDE⌝ : V) k)) + 7 +
      8 * (formulaLen LAct (instB (⌜qDG (TS gCu 1) (uS gCu 1) (wS gCu 1)⌝ : V) k) +
        formulaLen LAct (instB (⌜qTG (Semiterm.lMap swap (TS gCu 1)) (Semiterm.lMap swap (uS gCu 1)) (Semiterm.lMap swap (wS gCu 1))⌝ : V) k))
      + 7 ≤ k)
    (ha₂ : a + 8 * (formulaLen LAct (instB (⌜pG (TS gCu 1) (uS gCu 1) (wS gCu 1)⌝ : V) k) + formulaLen LAct (instB (⌜pCDE⌝ : V) k)) + 7 +
      8 * (formulaLen LAct (instB (⌜qCDE⌝ : V) k) + formulaLen LAct (instB (⌜Semiformula.lMap swap qCDE⌝ : V) k))
      + 7 ≤ k)
    (h : LenBoxUnbounded TAct a (instB (⌜pDCE⌝ : V) k)) :
    (EvalGraph 2 (DimcidV k) (SV gCu 1 k) (DimcidV k) 1 ∧ EvalGraph 2 (DimcidTV k) (SV gDu 0 k) (DimcidTV k) 0) ∧
    (EvalGraph 2 (SV gCu 1 k) (DimcidV k) (SV gCu 1 k) 1 ∧ EvalGraph 2 (SV gDu 0 k) (DimcidTV k) (SV gDu 0 k) 0) := by
  rw [instB_quote_pDCE] at h
  have hx := isFormula_instB_quote (pG (TS gCu 1) (uS gCu 1) (wS gCu 1)) k
  have hy := isFormula_instB_quote pCDE k
  have h₁ := lenBoxUnbounded_andL_V hx hy h
  have h₂ := lenBoxUnbounded_andR_V hx hy h
  obtain ⟨g1, g2⟩ := pG_both_V k (TS gCu 1) (uS gCu 1) (wS gCu 1) (hX_cupodE k) (hU_cupodE k) (hW_cupodE k) _ ha₁ h₁
  rw [transposeCode_cupodE] at g2
  have hx' := isFormula_instB_quote qCDE k
  have hy' := isFormula_instB_quote (Semiformula.lMap swap qCDE) k
  have h₂' : LenBoxUnbounded TAct
      (a + 8 * (formulaLen LAct (instB (⌜pG (TS gCu 1) (uS gCu 1) (wS gCu 1)⌝ : V) k) + formulaLen LAct (instB (⌜pCDE⌝ : V) k)) + 7)
      (instB (⌜qCDE⌝ : V) k ^⋏ instB (⌜Semiformula.lMap swap qCDE⌝ : V) k) := by
    rw [← instB_quote_pCDE]; exact h₂
  have c1 := lenBoxUnbounded_mono_V ha₂ (lenBoxUnbounded_andL_V hx' hy' h₂')
  have c2 := lenBoxUnbounded_mono_V ha₂ (lenBoxUnbounded_andR_V hx' hy' h₂')
  rw [lenBoxUnbounded_iff_lenBox, ← guardCode_cupodE_DimcidV_eq_instB] at c1
  rw [lenBoxUnbounded_iff_lenBox, ← guardCode_dupocE_DimcidTV_eq_instB] at c2
  have e1 := SV_search_V gCu 1 k (DimcidV k) c1
  have e2 := SV_search_V gDu 0 k (DimcidTV k) c2
  rw [Nat.cast_one] at e1
  rw [Nat.cast_zero] at e2
  exact ⟨⟨g1, g2⟩, ⟨e1, e2⟩⟩

/-- **The box form**: the two guards of the cell are provable within `k`. -/
theorem pDCE_guards_V (k a : V)
    (ha₁ : a + 8 * (formulaLen LAct (instB (⌜pG (TS gCu 1) (uS gCu 1) (wS gCu 1)⌝ : V) k) + formulaLen LAct (instB (⌜pCDE⌝ : V) k)) + 7 +
      8 * (formulaLen LAct (instB (⌜qDG (TS gCu 1) (uS gCu 1) (wS gCu 1)⌝ : V) k) +
        formulaLen LAct (instB (⌜qTG (Semiterm.lMap swap (TS gCu 1)) (Semiterm.lMap swap (uS gCu 1)) (Semiterm.lMap swap (wS gCu 1))⌝ : V) k))
      + 7 ≤ k)
    (ha₂ : a + 8 * (formulaLen LAct (instB (⌜pG (TS gCu 1) (uS gCu 1) (wS gCu 1)⌝ : V) k) + formulaLen LAct (instB (⌜pCDE⌝ : V) k)) + 7 +
      8 * (formulaLen LAct (instB (⌜qCDE⌝ : V) k) + formulaLen LAct (instB (⌜Semiformula.lMap swap qCDE⌝ : V) k))
      + 7 ≤ k)
    (h : LenBoxUnbounded TAct a (instB (⌜pDCE⌝ : V) k)) :
    LenBox TAct k (guardCode (⌜templateD⌝ : V) (DimcidV k) (SV gCu 1 k)) ∧
    LenBox TAct k (guardCode (⌜gCu⌝ : V) (SV gCu 1 k) (DimcidV k)) := by
  rw [instB_quote_pDCE] at h
  have hx := isFormula_instB_quote (pG (TS gCu 1) (uS gCu 1) (wS gCu 1)) k
  have hy := isFormula_instB_quote pCDE k
  have h₁ := lenBoxUnbounded_andL_V hx hy h
  have h₂ := lenBoxUnbounded_andR_V hx hy h
  obtain ⟨g1, _⟩ := pG_guards_V k (TS gCu 1) (uS gCu 1) (wS gCu 1) (hX_cupodE k) (hU_cupodE k) (hW_cupodE k) _ ha₁ h₁
  have hx' := isFormula_instB_quote qCDE k
  have hy' := isFormula_instB_quote (Semiformula.lMap swap qCDE) k
  have h₂' : LenBoxUnbounded TAct
      (a + 8 * (formulaLen LAct (instB (⌜pG (TS gCu 1) (uS gCu 1) (wS gCu 1)⌝ : V) k) + formulaLen LAct (instB (⌜pCDE⌝ : V) k)) + 7)
      (instB (⌜qCDE⌝ : V) k ^⋏ instB (⌜Semiformula.lMap swap qCDE⌝ : V) k) := by
    rw [← instB_quote_pCDE]; exact h₂
  have c1 := lenBoxUnbounded_mono_V ha₂ (lenBoxUnbounded_andL_V hx' hy' h₂')
  rw [lenBoxUnbounded_iff_lenBox, ← guardCode_cupodE_DimcidV_eq_instB] at c1
  exact ⟨g1, c1⟩

/-! #### `pDCE` in both readings -/

/-- `pDCE(k)` in the standard reading. -/
theorem eval_pDCE_iff_std (k : V) :
    Semiformula.Eval (s := stdReadingV V) ![k] Empty.elim pDCE ↔
      (((∃ n, EvalGraph n (DimcidV k) (SV gCu 1 k) (DimcidV k) 0) → (∃ n, EvalGraph n (SV gCu 1 k) (DimcidV k) (SV gCu 1 k) 1)) ∧
       ((∃ n, EvalGraph n (DimcidTV k) (SV gDu 0 k) (DimcidTV k) 1) → (∃ n, EvalGraph n (SV gDu 0 k) (DimcidTV k) (SV gDu 0 k) 0))) ∧
      ((∃ n, EvalGraph n (DimcidV k) (SV gCu 1 k) (DimcidV k) 1) ∧ (∃ n, EvalGraph n (DimcidTV k) (SV gDu 0 k) (DimcidTV k) 0)) := by
  rw [pDCE_def, pCDE_def]
  simp only [LogicalConnective.HomClass.map_and, LogicalConnective.Prop.and_eq]
  rw [eval_pG_iff_std k (TS gCu 1) (uS gCu 1) (wS gCu 1) (desc_cupodE k) (descT_cupodE k), eval_qCDE_iff_V,
    eval_qCDE_swapped_iff_V]

/-- `pDCE(k)` in the swapped reading: the SAME content (the conjuncts exchange roles). -/
theorem eval_pDCE_iff_swap (k : V) :
    Semiformula.Eval (s := swappedReading V) ![k] Empty.elim pDCE ↔
      (((∃ n, EvalGraph n (DimcidV k) (SV gCu 1 k) (DimcidV k) 0) → (∃ n, EvalGraph n (SV gCu 1 k) (DimcidV k) (SV gCu 1 k) 1)) ∧
       ((∃ n, EvalGraph n (DimcidTV k) (SV gDu 0 k) (DimcidTV k) 1) → (∃ n, EvalGraph n (SV gDu 0 k) (DimcidTV k) (SV gDu 0 k) 0))) ∧
      ((∃ n, EvalGraph n (DimcidV k) (SV gCu 1 k) (DimcidV k) 1) ∧ (∃ n, EvalGraph n (DimcidTV k) (SV gDu 0 k) (DimcidTV k) 0)) := by
  rw [eval_swappedReading, pDCE_def, LogicalConnective.HomClass.map_and, lMap_swap_pG, lMap_swap_pCDE,
    ← stdReadingV_eq_stdReading]
  simp only [LogicalConnective.HomClass.map_and, LogicalConnective.Prop.and_eq]
  rw [eval_qDG_iff_V k (TS gCu 1) (uS gCu 1) (wS gCu 1) (desc_cupodE k), eval_qTG_iff_V k _ _ _ (descT_cupodE k),
    eval_qCDE_iff_V, eval_qCDE_swapped_iff_V,
    and_comm (a := ∃ n, EvalGraph n (DimcidTV k) (SV gDu 0 k) (DimcidTV k) 0),
    and_comm (a := (∃ n, EvalGraph n (DimcidTV k) (SV gDu 0 k) (DimcidTV k) 1) → _)]

theorem eval_pDCE_iff_stdReading (k : V) :
    Semiformula.Eval (s := stdReading V) ![k] Empty.elim pDCE ↔
      (((∃ n, EvalGraph n (DimcidV k) (SV gCu 1 k) (DimcidV k) 0) → (∃ n, EvalGraph n (SV gCu 1 k) (DimcidV k) (SV gCu 1 k) 1)) ∧
       ((∃ n, EvalGraph n (DimcidTV k) (SV gDu 0 k) (DimcidTV k) 1) → (∃ n, EvalGraph n (SV gDu 0 k) (DimcidTV k) (SV gDu 0 k) 0))) ∧
      ((∃ n, EvalGraph n (DimcidV k) (SV gCu 1 k) (DimcidV k) 1) ∧ (∃ n, EvalGraph n (DimcidTV k) (SV gDu 0 k) (DimcidTV k) 0)) := by
  rw [← stdReadingV_eq_stdReading]; exact eval_pDCE_iff_std k

end family

/-! ### 4. The Löb premise and the cell -/

section cell

/-- **The bounded Löb premise of the mutual family, slack `(14, 16)`**: a box of `pDCE(k)` makes all four
searchers find their guards (fuel 2); DIMCID's implications hold because the engine Cupod/Dupoc actually
play the consequents, and their guards are the plays of DIMCID/its transposition — true in both
readings. -/
theorem loebSound_pDCE : LoebSound pDCE 14 16 := by
  intro V _ _ k a ha h
  have : V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁ := inferInstance
  have ha₁ := le_trans (slack4_le a _ _ _ _ _ (formulaLen_instB_pG (TS gCu 1) (uS gCu 1) (wS gCu 1) k)
    (formulaLen_instB_pDCE k)) ha
  have ha₂ := le_trans (slack4_le' a _ _ _ _ _ (formulaLen_instB_pCDE k) (formulaLen_instB_pDCE k)) ha
  obtain ⟨⟨g1, g2⟩, ⟨c1, c2⟩⟩ := pDCE_all_V k a ha₁ ha₂ h
  exact ⟨(eval_pDCE_iff_stdReading k).mpr ⟨⟨fun _ ↦ ⟨2, c1⟩, fun _ ↦ ⟨2, c2⟩⟩, ⟨⟨2, g1⟩, ⟨2, g2⟩⟩⟩,
    (eval_pDCE_iff_swap k).mpr ⟨⟨fun _ ↦ ⟨2, c1⟩, fun _ ↦ ⟨2, c2⟩⟩, ⟨⟨2, g1⟩, ⟨2, g2⟩⟩⟩⟩

/-- **The DIMCID × CupodBot cell, packaged**: for all large `k`, DIMCID defects against the engine Cupod
and the engine Cupod defects against DIMCID (fuel 2), and both guard boxes hold — `family_found pDCE`
then the two-level ∧-elimination on codes. -/
theorem loeb_DIMCID_vs_CupodBot_core_of_nec {d : ℕ} (hE : BoundedInnerNec d) :
    ∃ k₀ : ℕ, ∀ k : ℕ, k₀ < k →
      (EvalGraph 2 (Dimcid k) (SV (V := ℕ) gCu 1 k) (Dimcid k) 1 ∧
        EvalGraph 2 (SV (V := ℕ) gCu 1 k) (Dimcid k) (SV (V := ℕ) gCu 1 k) 1) ∧
      (LenBox TAct k (guardCode (⌜templateD⌝ : ℕ) (Dimcid k) (SV (V := ℕ) gCu 1 k)) ∧
        LenBox TAct k (guardCode (⌜gCu⌝ : ℕ) (SV (V := ℕ) gCu 1 k) (Dimcid k))) := by
  obtain ⟨k₀, h⟩ := family_found pDCE hE loebSound_pDCE
  refine ⟨k₀, fun k hk ↦ ?_⟩
  obtain ⟨a, ha, hpc⟩ := h k hk
  have ha₁ := le_def.mpr (slack4_nat a _ _ _ _ _ k (formulaLen_instB_pG (V := ℕ) (TS gCu 1) (uS gCu 1) (wS gCu 1) k)
    (formulaLen_instB_pDCE (V := ℕ) k) ha)
  have ha₂ := le_def.mpr (slack4_nat' a _ _ _ _ _ k (formulaLen_instB_pCDE (V := ℕ) k)
    (formulaLen_instB_pDCE (V := ℕ) k) ha)
  obtain ⟨⟨g1, _⟩, ⟨c1, _⟩⟩ := pDCE_all_V (V := ℕ) k a ha₁ ha₂ hpc
  exact ⟨⟨g1, c1⟩, pDCE_guards_V (V := ℕ) k a ha₁ ha₂ hpc⟩

/-- **DIMCID × CupodBot is `(D, D)` in PA-`S'`, on the ENGINE's codes, unconditional**: for all large `k`,
`progCode (DIMCID k)` defects against `progCode (CupodBot k)` and `progCode (CupodBot k)` defects against
`progCode (DIMCID k)` (fuel 2). The engine's `outcome_DIMCID_vs_CupodBot = (D, D)` (`mutual_pblt_engine_id`)
agrees. -/
theorem loeb_DIMCID_vs_CupodBot :
    ∃ k₀ : ℕ, ∀ k : ℕ, k₀ < k →
      EvalGraph 2 (progCode (DIMCID k)) (progCode (CupodBot k)) (progCode (DIMCID k)) (actCode .D) ∧
      EvalGraph 2 (progCode (CupodBot k)) (progCode (DIMCID k)) (progCode (CupodBot k)) (actCode .D) := by
  obtain ⟨k₀, h⟩ := loeb_DIMCID_vs_CupodBot_core_of_nec boundedInnerNec_sixteen
  exact ⟨k₀, fun k hk ↦ by rw [progCode_DIMCID, progCode_CupodBot_SV]; exact (h k hk).1⟩


end cell

end ArithS
