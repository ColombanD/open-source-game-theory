import ArithS.Necessitation.Package
import PrisonersDilemma.Bots.LlmGenerations.DIMCID
import ArithS.Cells.Common.Templates
import ArithS.Cells.Common.Probers
import ArithS.Cells.Common.Families
import ArithS.Cells.Common.Khat
import ArithS.Assembly.Cell
import ArithS.Eval.SimTest

/-!
# ArithS.Cells.DIMCID — DIMCID × DIMCID, DIMCID × Mirror and DIMCID × Cupod, all `(D, D)`, in PA-`S'`

`Research/Notes/ROUTE_B_SCOPE.md` §3 Phase 2: the DIMCID family — the arithmetized
twins of the engine's `llm_outcome_DIMCID_vs_DIMCID = (D, D)` (`pblt_engine`),
`llm_outcome_DIMCID_vs_MirrorBot = (D, D)` and `outcome_DIMCID_vs_CupodBot = (D, D)`
(`mutual_pblt_engine_id`). The engine's bot is
`DIMCID k := .search k (.impl (.plays .self .opp C) (.plays .opp .self D)) (.const D) (.const C)`
("if I can prove that my cooperating implies your defecting, defect; else cooperate"). Löb: a
proof of the guard within the budget makes DIMCID DEFECT, which makes the guard's consequent
"opp plays D against me" TRUE against itself (and against Mirror, which copies), so the guard —
an implication — is true; the fixed point closes it. The pattern is `Cells/DupocMirror.lean`
(V-generic bot code, description term, guard as a `k`-instance of a fixed formula, truth
equations in both readings, search clauses, conjunction family, `LoebSound`, then
`Assembly/Family.family_found` and the cells at `ℕ`), with two differences:

1. **The guard is the GENERAL translation `template`** (`Code.lean`), not the hand-written `guardTemplate`:
   `templateD := template phiD` with `phiD := .impl (.plays .self .opp C) (.plays .opp .self D)`, a closed
   constant never evaluated; `DimcidV k := pSearch k ⌜templateD⌝ (pConst 1) (pConst 0)` and
   `progCode (PD.Bots.DIMCID k) = Dimcid k` (`progCode_DIMCID`, the bridge to the engine). Its
   transposition is the searcher on `templateDT := template phiD.transpose` with the branches swapped
   (`transposeCode_DimcidV`, via `lMap_swap_template` on the fragment) — τ(DIMCID) is not a zoo bot, and
   need not be: the swap reading of every fixed formula is handled by the transposed code exactly
   as `eval_qDM_swap_iff_V`. The canonical description (`innerDi`/`innerDT` irreducible, `gDi pDi
   qDi`, `uDi wDi`, the tower `TDi`, `canonical_DimcidV`/`revalueU_DimcidV`/`revalueW_DimcidV`, `val_TDi_V`,
   `revalue_val_uDi_wDi_V`, `revalue_val_uDiT_wDiT_V`) is `Instance`/`InstanceV` §2, `Transparency`
   §1 and `Prep` §2 re-run on the new constants.
2. **The truth of `template` at a PRONOUN atom, in every model** (§3, NEW): `Det.models_sentenceAt_plays_V`
   handles the `.plays` clause only for PROPER programs (`closedDesc`); DIMCID's guard has the bare
   pronouns `.self`/`.opp` (`progAux_self`/`progAux_opp`, the `descF` shape on the frame variables).
   `eval_template_plays_self_opp_V`/`eval_template_plays_opp_self_V`: at the frame
   `b = (x₁, u₁, w₁, x₂, u₂, w₂)`, "`revalue u₁ w₁ x₁` plays `a` against `revalue u₂ w₂ x₂`" (and
   symmetrically) — by `Semiformula.eval_substs` on the ∃-prefix, `eval_relDesc_V`/`eval_evalG_V`
   (`Det.lean`, already V-generic) and the `Matrix.cons_val` simproc. Then `eval_templateD_V`/
   `eval_templateDT_V`: the template is the implication of the two atoms. Nothing in `Code.lean`/
   `Agent.lean`/`Det.lean`/`Instance*.lean` was changed.

The fixed formulas are stated GENERICALLY in the opponent's description triple `(X, U, W)` (`X` a
one-variable term in the budget, `U W` closed): `qDG X U W := templateD ⇜ ![TDi, cl uDi, cl wDi, X,
cl U, cl W]` and the transposed `qTG`, with `lMap swap (qDG X U W) = qTG (swap X) (swap U) (swap W)`;
the truth equations (`eval_qDG_iff_V`, `eval_qTG_iff_V`) take the hypothesis "the triple describes
`opp` in `stdReadingV V`", the instance equations on codes (`guardCode_DimcidV_eq_instB`,
`guardCode_DimcidTV_eq_instB` — the latter via `revalueTemplate_substTemplate`, as `Prep` §1) take the
three code-level description hypotheses, and the conjunction family `pG X U W := qDG X U W ⋏ qTG
(swap X) (swap U) (swap W)` (the `Prep` §3 / `DupocMirror` §5 move) gives `pG_both_V`/`pG_guards_V`
by ∧-elimination on codes and `eval_pG_iff_std/_swap` (the same content in both readings). A cell
is then the five hypotheses for its opponent plus `LoebSound _ 7 8`:
* **Cell 1 (§7)**: `(TDi, uDi, wDi)` describes `DimcidV k` itself; `qDD`, `pDD`, `loebSound_pDD`,
  `loeb_Dimcid_vs_Dimcid_core_of_nec`, **`loeb_Dimcid_vs_Dimcid`** (`EvalGraph 2 (Dimcid k)
  (Dimcid k) (Dimcid k) 1` for all large `k`), `loeb_Dimcid_vs_Dimcid_guard` (the box form),
  and the engine-facing `loeb_DIMCID_vs_DIMCID_guardOf` (`Agent.guardOf phiD (DIMCID k)
  (DIMCID k)` is `TAct`-provable within `k`).
* **Cell 2 (§8)**: `(cl TM, numT 0, numT 1)` describes `MirrorV` (`Cells/DupocMirror`, reused: `TM`,
  `MirrorV`, `mirror_step_V`); `qDMi`, `pDMi`, `loebSound_pDMi` (Mirror COPIES at fuel 3, the
  generic `mirror_copies2_V`), **`loeb_Dimcid_vs_Mirror`** (`Dimcid k` defects at fuel 2
  and Mirror defects back at fuel 3), `loeb_Dimcid_vs_Mirror_guard`.
* **Cell 3 (§9), the MUTUAL family** (the engine's `outcome_DIMCID_vs_CupodBot = (D, D)`,
  `mutual_pblt_engine_id`): `(TD, uC, wC)` describes `CupodV k` (`revalueU_CupodV`/`revalueW_CupodV`,
  `canonical_CupodV_eq`, new here) and its transposition describes `DupocV k`. DIMCID's guard against
  Cupod says "Cupod plays D against me", which Cupod only does if IT finds ITS guard ("DIMCID plays D
  against me") — so the family is the four-guard conjunction `pDC := pG TD uC wC ⋏ pCD`, `pCD := qCD
  ⋏ lMap swap qCD`, with `qCD := qG 1 TD uC wC TDi uDi wDi` Cupod's guard against DIMCID on the
  hand-written template (`qG a X U W X' U' W' := guardTemplate a ⇜ ![X, cl U, cl W, X', cl U', cl W']`, the
  fully generic instance equation `guardCode_GtmplA_eq_instB` / `_swap_eq_instB` and truth equation
  `eval_qG_iff_V`, both taking description hypotheses — `InstanceV` §4 / `DupocMirror` §2–3 with both
  triples as parameters). A box of `pDC(k)` yields the four guard boxes by a TWO-level ∧-elimination
  (`pDC_all_V`, slack `(14, 16)`: `slack4_le`/`slack4_nat`), so all four searchers commit at fuel 2 —
  DIMCID defects against Cupod, Cupod defects against DIMCID, the transposed searcher cooperates with
  Dupoc, Dupoc cooperates with it — which makes every conjunct true in both readings
  (`loebSound_pDC : LoebSound pDC 14 16`); **`loeb_Dimcid_vs_Cupod`** (both defect at
  fuel 2) and `loeb_Dimcid_vs_Cupod_guards` (both boxes).

Conventions (`HANDOVER_ARITHMETIZED_S.md` §5–6): every threshold and constant is EXISTENTIAL; `simp`
never sees a closed quote of `templateD`/`qDD`/`pDD` (the quote equations are for VARIABLE sentences,
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

/-- DIMCID's guard: "my cooperating implies your defecting". -/
def phiD : PD.Formula := .impl (.plays .self .opp .C) (.plays .opp .self .D)


lemma fragF_phiD : fragF phiD = true := rfl

/-- The six-variable template of DIMCID's guard (a CLOSED constant, never evaluated). -/
noncomputable def templateD : Semisentence LAct 6 := template phiD

/-- The template of the transposed guard. -/
noncomputable def templateDT : Semisentence LAct 6 := template phiD.transpose

lemma templateD_eq : templateD = template (.plays .self .opp .C) 🡒 template (.plays .opp .self .D) := template_impl _ _

lemma templateDT_eq : templateDT = template (.plays .self .opp .D) 🡒 template (.plays .opp .self .C) := template_impl _ _

lemma lMap_swap_templateD : Semiformula.lMap swap templateD = templateDT := lMap_swap_template phiD fragF_phiD

lemma lMap_swap_templateDT : Semiformula.lMap swap templateDT = templateD := by
  rw [← lMap_swap_templateD, lMap_swap_swap]


end template

/-! ### 1. DIMCID in every model, and its transposition -/

section dimcid

/-- `DIMCID k` in an arbitrary model: search the guard within budget `k`; found ⇒ `D` (`pConst 1`),
else `C` (`pConst 0`). -/
noncomputable def DimcidV (k : V) : V := pSearch k (⌜templateD⌝ : V) (pConst 1) (pConst 0)

/-- The transposed searcher (τ(DIMCID)): its guard is the transposed template, found ⇒ `C`. -/
noncomputable def DimcidTV (k : V) : V := pSearch k (⌜templateDT⌝ : V) (pConst 0) (pConst 1)


/-- `DIMCID k` at `ℕ`. -/
noncomputable def Dimcid (k : ℕ) : ℕ := DimcidV (V := ℕ) k


/-- **The bridge to the engine**: the code of the engine's `DIMCID k` is `Dimcid k`. -/
theorem progCode_DIMCID (k : ℕ) : progCode (PD.Bots.DIMCID k) = Dimcid k := by
  rw [PD.Bots.DIMCID, progCode_search_noSnap _ _ _ _ rfl]; simp only [progCode_const, actCode]
  change pSearch k (templateCode phiD) _ _ = _
  rw [templateCode_eq_quote_template phiD (noSelfIdxF_of_fragF _ fragF_phiD)]; rfl

theorem transposeCode_DimcidV (k : V) : transposeCode (DimcidV k) = DimcidTV k := by
  unfold DimcidV DimcidTV transposeCode
  rw [revalue_search, revalue_const, revalue_const, revalueTemplate_quote_sentence₆_V, lMap_swap_templateD]
  simp [revalueAction]


end dimcid

/-! ### 2. The canonical description of `DimcidV k` is `k`-independent apart from the budget -/

section canonical

/-- The budget-independent inner part of DIMCID's code. -/
noncomputable def innerDi : ℕ := ppair (⌜templateD⌝ : ℕ) (ppair (pConst 1) (pConst 0))

/-- The budget-independent inner part of the transposed searcher's code. -/
noncomputable def innerDT : ℕ := ppair (⌜templateDT⌝ : ℕ) (ppair (pConst 0) (pConst 1))

lemma innerDi_def : innerDi = ppair (⌜templateD⌝ : ℕ) (ppair (pConst 1) (pConst 0)) := rfl
lemma innerDT_def : innerDT = ppair (⌜templateDT⌝ : ℕ) (ppair (pConst 0) (pConst 1)) := rfl

/- Closed constants built from the giant templates: never to be evaluated. -/
attribute [irreducible] innerDi innerDT

lemma cast_innerDi : ((innerDi : ℕ) : V) = ppair (⌜templateD⌝ : V) (ppair (pConst 1) (pConst 0)) := by
  rw [innerDi_def, cast_ppair, cast_ppair, cast_pConst, cast_pConst, coe_quote_sentence₆]
  push_cast
  rfl

lemma cast_innerDT : ((innerDT : ℕ) : V) = ppair (⌜templateDT⌝ : V) (ppair (pConst 0) (pConst 1)) := by
  rw [innerDT_def, cast_ppair, cast_ppair, cast_pConst, cast_pConst, coe_quote_sentence₆]
  push_cast
  rfl

lemma DimcidV_eq_inner (k : V) : DimcidV k = ppair 6 (ppair k (innerDi : V)) + 1 := by
  rw [cast_innerDi]; rfl
lemma DimcidTV_eq_inner (k : V) : DimcidTV k = ppair 6 (ppair k (innerDT : V)) + 1 := by
  rw [cast_innerDT]; rfl

lemma DimcidV_lt_DimcidTV_iff (k : V) : DimcidV k < DimcidTV k ↔ innerDi < innerDT := by
  rw [DimcidV_eq_inner, DimcidTV_eq_inner, pSearchInner_lt_iff, Nat.cast_lt]

lemma DimcidTV_lt_DimcidV_iff (k : V) : DimcidTV k < DimcidV k ↔ innerDT < innerDi := by
  rw [DimcidV_eq_inner, DimcidTV_eq_inner, pSearchInner_lt_iff, Nat.cast_lt]

/-- The stored template of the canonical searcher (`⌜templateD⌝` or `⌜templateDT⌝`). -/
noncomputable def gDi : ℕ := if innerDi ≤ innerDT then (⌜templateD⌝ : ℕ) else (⌜templateDT⌝ : ℕ)
/-- Its then-branch. -/
noncomputable def pDi : ℕ := if innerDi ≤ innerDT then pConst 1 else pConst 0
/-- Its else-branch. -/
noncomputable def qDi : ℕ := if innerDi ≤ innerDT then pConst 0 else pConst 1
/-- The first re-valuation term of the description of `DimcidV k`. -/
noncomputable def uDi : ClosedSemiterm LAct 0 :=
  if innerDi < innerDT then cterm Act.C else if innerDT < innerDi then cterm Act.D else numT 0
/-- The second re-valuation term of the description of `DimcidV k`. -/
noncomputable def wDi : ClosedSemiterm LAct 0 :=
  if innerDi < innerDT then cterm Act.D else if innerDT < innerDi then cterm Act.C else numT 1

lemma DimcidV_eq_cast (k : V) :
    DimcidV k = pSearch k ((⌜templateD⌝ : ℕ) : V) ((pConst 1 : ℕ) : V) ((pConst 0 : ℕ) : V) := by
  unfold DimcidV; rw [coe_quote_sentence₆, cast_pConst, cast_pConst]; push_cast; rfl

lemma DimcidTV_eq_cast (k : V) :
    DimcidTV k = pSearch k ((⌜templateDT⌝ : ℕ) : V) ((pConst 0 : ℕ) : V) ((pConst 1 : ℕ) : V) := by
  unfold DimcidTV; rw [coe_quote_sentence₆, cast_pConst, cast_pConst]; push_cast; rfl

/-- **The canonical code of `DimcidV k` is a searcher with the (cast) `k`-independent inner triple.** -/
theorem canonical_DimcidV (k : V) : canonical (DimcidV k) = pSearch k (gDi : V) (pDi : V) (qDi : V) := by
  by_cases h : innerDi ≤ innerDT
  · simp only [gDi, pDi, qDi, if_pos h]
    rcases Nat.lt_or_eq_of_le h with h' | h'
    · rw [canonical_of_lt (by rw [transposeCode_DimcidV]; exact (DimcidV_lt_DimcidTV_iff k).mpr h')]
      exact DimcidV_eq_cast k
    · rw [canonical_of_eq (by rw [transposeCode_DimcidV, DimcidV_eq_inner, DimcidTV_eq_inner, h'])]
      exact DimcidV_eq_cast k
  · simp only [gDi, pDi, qDi, if_neg h]
    rw [canonical_of_gt (by rw [transposeCode_DimcidV]; exact (DimcidTV_lt_DimcidV_iff k).mpr (Nat.lt_of_not_le h)),
      transposeCode_DimcidV]
    exact DimcidTV_eq_cast k

theorem revalueU_DimcidV (k : V) : revalueU (DimcidV k) = (⌜uDi⌝ : V) := by
  unfold revalueU uDi
  rw [transposeCode_DimcidV]
  by_cases h1 : innerDi < innerDT
  · rw [if_pos ((DimcidV_lt_DimcidTV_iff k).mpr h1), if_pos h1, quote_cterm_C]
  · rw [if_neg (fun h ↦ h1 ((DimcidV_lt_DimcidTV_iff k).mp h)), if_neg h1]
    by_cases h2 : innerDT < innerDi
    · rw [if_pos ((DimcidTV_lt_DimcidV_iff k).mpr h2), if_pos h2, quote_cterm_D]
    · rw [if_neg (fun h ↦ h2 ((DimcidTV_lt_DimcidV_iff k).mp h)), if_neg h2, quote_numT]
      simp

theorem revalueW_DimcidV (k : V) : revalueW (DimcidV k) = (⌜wDi⌝ : V) := by
  unfold revalueW wDi
  rw [transposeCode_DimcidV]
  by_cases h1 : innerDi < innerDT
  · rw [if_pos ((DimcidV_lt_DimcidTV_iff k).mpr h1), if_pos h1, quote_cterm_D]
  · rw [if_neg (fun h ↦ h1 ((DimcidV_lt_DimcidTV_iff k).mp h)), if_neg h1]
    by_cases h2 : innerDT < innerDi
    · rw [if_pos ((DimcidTV_lt_DimcidV_iff k).mpr h2), if_pos h2, quote_cterm_C]
    · rw [if_neg (fun h ↦ h2 ((DimcidTV_lt_DimcidV_iff k).mp h)), if_neg h2, quote_numT]
      simp

/-- The one-variable description term of DIMCID, over `LAct`. -/
noncomputable def TDi : Semiterm LAct Empty 1 := Semiterm.lMap emb (searchT1 gDi pDi qDi)

lemma lMap_swap_TDi : Semiterm.lMap swap TDi = TDi := term_lMap_swap_emb _

/-- The code of `TDi` (over `LAct`) is the `ℒₒᵣ` tower. -/
theorem quote_emb_TDi :
    (⌜(Rew.emb TDi : SyntacticSemiterm LAct 1)⌝ : V) =
    ppairTerm (binNumeral 6) (ppairTerm (^#0) (ppairTerm (binNumeral (gDi : V)) (ppairTerm (codeTerm (pDi : V)) (codeTerm (qDi : V))))) ^+ 𝟏 := by
  unfold TDi
  rw [term_emb_lMap_emb_n, quote_term_lMap_emb, quote_emb_searchT1]

/-- **`TDi` at the budget `k` denotes the canonical code of `DimcidV k`** (in `stdReadingV V`). -/
theorem val_TDi_V (k : V) : TDi.val (s := stdReadingV V) ![k] Empty.elim = canonical (DimcidV k) := by
  unfold TDi
  rw [Semiterm.val_lMap, stdReadingV_lMap_emb, val_searchT1_V, canonical_DimcidV]

/-- The `k`-independent re-valuation terms reconstruct `DimcidV k` from its canonical code. -/
theorem revalue_val_uDi_wDi_V (k : V) :
    revalue (uDi.val (s := stdReadingV V) ![] Empty.elim) (wDi.val (s := stdReadingV V) ![] Empty.elim)
      (canonical (DimcidV k)) = DimcidV k := by
  unfold uDi wDi
  by_cases h1 : innerDi < innerDT
  · rw [if_pos h1, if_pos h1, val_cterm_C_V, val_cterm_D_V,
      canonical_of_lt (by rw [transposeCode_DimcidV]; exact (DimcidV_lt_DimcidTV_iff k).mpr h1), revalue_zero_one]
  · rw [if_neg h1, if_neg h1]
    by_cases h2 : innerDT < innerDi
    · rw [if_pos h2, if_pos h2, val_cterm_D_V, val_cterm_C_V,
        canonical_of_gt (by rw [transposeCode_DimcidV]; exact (DimcidTV_lt_DimcidV_iff k).mpr h2)]
      exact transposeCode_transposeCode _
    · have h' : innerDi = innerDT := le_antisymm (not_lt.mp h2) (not_lt.mp h1)
      rw [if_neg h2, if_neg h2, val_numT_V, val_numT_V, Nat.cast_zero, Nat.cast_one,
        canonical_of_eq (by rw [transposeCode_DimcidV, DimcidV_eq_inner, DimcidTV_eq_inner, h']), revalue_zero_one]

/-- The transposed re-valuation terms. -/
noncomputable def uDiT : ClosedSemiterm LAct 0 := Semiterm.lMap swap uDi
noncomputable def wDiT : ClosedSemiterm LAct 0 := Semiterm.lMap swap wDi

/-- The transposed descriptions reconstruct `DimcidTV k` from the canonical code of `DimcidV k`. -/
theorem revalue_val_uDiT_wDiT_V (k : V) :
    revalue (uDiT.val (s := stdReadingV V) ![] Empty.elim) (wDiT.val (s := stdReadingV V) ![] Empty.elim)
      (canonical (DimcidV k)) = DimcidTV k := by
  unfold uDiT wDiT uDi wDi
  by_cases h1 : innerDi < innerDT
  · rw [if_pos h1, if_pos h1, lMap_swap_cterm_C, lMap_swap_cterm_D, val_cterm_D_V, val_cterm_C_V,
      canonical_of_lt (by rw [transposeCode_DimcidV]; exact (DimcidV_lt_DimcidTV_iff k).mpr h1)]
    exact transposeCode_DimcidV k
  · rw [if_neg h1, if_neg h1]
    by_cases h2 : innerDT < innerDi
    · rw [if_pos h2, if_pos h2, lMap_swap_cterm_D, lMap_swap_cterm_C, val_cterm_C_V, val_cterm_D_V,
        canonical_of_gt (by rw [transposeCode_DimcidV]; exact (DimcidTV_lt_DimcidV_iff k).mpr h2), transposeCode_DimcidV,
        revalue_zero_one]
    · have h' : innerDi = innerDT := le_antisymm (not_lt.mp h2) (not_lt.mp h1)
      have hDT : DimcidV k = DimcidTV k := by rw [DimcidV_eq_inner, DimcidTV_eq_inner, h']
      rw [if_neg h2, if_neg h2, lMap_swap_numT, lMap_swap_numT, val_numT_V, val_numT_V, Nat.cast_zero,
        Nat.cast_one, canonical_of_eq (by rw [transposeCode_DimcidV, hDT]), revalue_zero_one, hDT]

end canonical

/-! ### 3. The pronoun atoms of `template` in every model, and the truth of the guard template -/

section atoms


/-- **The truth of DIMCID's guard template at a frame**: "me plays C against opp" implies "opp
plays D against me". -/
theorem eval_templateD_V (b : Fin 6 → V) :
    Semiformula.Eval (s := stdReadingV V) b Empty.elim templateD ↔
      ((∃ n, EvalGraph n (revalue (b 1) (b 2) (b 0)) (revalue (b 4) (b 5) (b 3)) (revalue (b 1) (b 2) (b 0)) 0) →
        (∃ n, EvalGraph n (revalue (b 4) (b 5) (b 3)) (revalue (b 1) (b 2) (b 0)) (revalue (b 4) (b 5) (b 3)) 1)) := by
  rw [templateD_eq]
  simp only [LogicalConnective.HomClass.map_imply, LogicalConnective.Prop.arrow_eq,
    eval_template_plays_self_opp_V, eval_template_plays_opp_self_V, actCode, Nat.cast_zero, Nat.cast_one]

/-- **The truth of the transposed guard template at a frame**: "me plays D against opp" implies
"opp plays C against me". -/
theorem eval_templateDT_V (b : Fin 6 → V) :
    Semiformula.Eval (s := stdReadingV V) b Empty.elim templateDT ↔
      ((∃ n, EvalGraph n (revalue (b 1) (b 2) (b 0)) (revalue (b 4) (b 5) (b 3)) (revalue (b 1) (b 2) (b 0)) 1) →
        (∃ n, EvalGraph n (revalue (b 4) (b 5) (b 3)) (revalue (b 1) (b 2) (b 0)) (revalue (b 4) (b 5) (b 3)) 0)) := by
  rw [templateDT_eq]
  simp only [LogicalConnective.HomClass.map_imply, LogicalConnective.Prop.arrow_eq,
    eval_template_plays_self_opp_V, eval_template_plays_opp_self_V, actCode, Nat.cast_zero, Nat.cast_one]

end atoms

/-! ### 4. The fixed formulas, generic in the opponent's description triple -/

section fixedFormulas

/-- **The fixed formula of DIMCID against an opponent described by `(X, U, W)`** (`X` a one-variable
term in the budget, `U W` closed): `templateD` filled with DIMCID's description in the me-slots. -/
noncomputable def qDG (X : Semiterm LAct Empty 1) (U W : ClosedSemiterm LAct 0) : Semisentence LAct 1 :=
  templateD ⇜ ![TDi, cl uDi, cl wDi, X, cl U, cl W]

/-- **The fixed formula of the transposed searcher** against `(X, U, W)`. -/
noncomputable def qTG (X : Semiterm LAct Empty 1) (U W : ClosedSemiterm LAct 0) : Semisentence LAct 1 :=
  templateDT ⇜ ![TDi, cl uDiT, cl wDiT, X, cl U, cl W]

lemma lMap_swap_qDG (X : Semiterm LAct Empty 1) (U W : ClosedSemiterm LAct 0) :
    Semiformula.lMap swap (qDG X U W) =
      qTG (Semiterm.lMap swap X) (Semiterm.lMap swap U) (Semiterm.lMap swap W) := by
  unfold qDG qTG
  rw [Semiformula.lMap_subst, lMap_swap_templateD]
  congr 1
  funext i
  fin_cases i <;> simp [lMap_swap_TDi, lMap_swap_cl, uDiT, wDiT]

lemma lMap_swap_qTG (X : Semiterm LAct Empty 1) (U W : ClosedSemiterm LAct 0) :
    Semiformula.lMap swap (qTG X U W) =
      qDG (Semiterm.lMap swap X) (Semiterm.lMap swap U) (Semiterm.lMap swap W) := by
  unfold qDG qTG
  rw [Semiformula.lMap_subst, lMap_swap_templateDT]
  congr 1
  funext i
  fin_cases i <;> simp [lMap_swap_TDi, lMap_swap_cl, uDiT, wDiT, term_lMap_swap_swap]

/-- **The truth equation of `qDG X U W` in every model** (standard reading), given that the triple
describes `opp` at the budget `k`: "`DimcidV k` plays C against `opp`" implies "`opp` plays D
against `DimcidV k`". -/
theorem eval_qDG_iff_V (k : V) (X : Semiterm LAct Empty 1) (U W : ClosedSemiterm LAct 0) {opp : V}
    (hopp : revalue (U.val (s := stdReadingV V) ![] Empty.elim) (W.val (s := stdReadingV V) ![] Empty.elim)
      (X.val (s := stdReadingV V) ![k] Empty.elim) = opp) :
    Semiformula.Eval (s := stdReadingV V) ![k] Empty.elim (qDG X U W) ↔
      ((∃ n, EvalGraph n (DimcidV k) opp (DimcidV k) 0) → (∃ n, EvalGraph n opp (DimcidV k) opp 1)) := by
  unfold qDG
  rw [Semiformula.eval_substs]
  have h0 : (Semiterm.val (s := stdReadingV V) ![k] Empty.elim ∘ ![TDi, cl uDi, cl wDi, X, cl U, cl W]) =
      ![canonical (DimcidV k), uDi.val (s := stdReadingV V) ![] Empty.elim, wDi.val (s := stdReadingV V) ![] Empty.elim,
        X.val (s := stdReadingV V) ![k] Empty.elim, U.val (s := stdReadingV V) ![] Empty.elim,
        W.val (s := stdReadingV V) ![] Empty.elim] := by
    funext i; fin_cases i <;> simp [val_TDi_V, val_cl_V]
  rw [h0, eval_templateD_V]
  simp only [Matrix.cons_val]
  rw [revalue_val_uDi_wDi_V, hopp]

/-- **The truth equation of `qTG X U W` in every model** (standard reading): "`DimcidTV k` plays D
against `opp`" implies "`opp` plays C against `DimcidTV k`". -/
theorem eval_qTG_iff_V (k : V) (X : Semiterm LAct Empty 1) (U W : ClosedSemiterm LAct 0) {opp : V}
    (hopp : revalue (U.val (s := stdReadingV V) ![] Empty.elim) (W.val (s := stdReadingV V) ![] Empty.elim)
      (X.val (s := stdReadingV V) ![k] Empty.elim) = opp) :
    Semiformula.Eval (s := stdReadingV V) ![k] Empty.elim (qTG X U W) ↔
      ((∃ n, EvalGraph n (DimcidTV k) opp (DimcidTV k) 1) → (∃ n, EvalGraph n opp (DimcidTV k) opp 0)) := by
  unfold qTG
  rw [Semiformula.eval_substs]
  have h0 : (Semiterm.val (s := stdReadingV V) ![k] Empty.elim ∘ ![TDi, cl uDiT, cl wDiT, X, cl U, cl W]) =
      ![canonical (DimcidV k), uDiT.val (s := stdReadingV V) ![] Empty.elim, wDiT.val (s := stdReadingV V) ![] Empty.elim,
        X.val (s := stdReadingV V) ![k] Empty.elim, U.val (s := stdReadingV V) ![] Empty.elim,
        W.val (s := stdReadingV V) ![] Empty.elim] := by
    funext i; fin_cases i <;> simp [val_TDi_V, val_cl_V]
  rw [h0, eval_templateDT_V]
  simp only [Matrix.cons_val]
  rw [revalue_val_uDiT_wDiT_V, hopp]

omit [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁] in
/-- The swapped reading of `qDG` is the standard reading of the transposed `qTG`. -/
theorem eval_qDG_swap_iff_V (k : V) (X : Semiterm LAct Empty 1) (U W : ClosedSemiterm LAct 0) :
    Semiformula.Eval (s := swappedReading V) ![k] Empty.elim (qDG X U W) ↔
      Semiformula.Eval (s := stdReadingV V) ![k] Empty.elim
        (qTG (Semiterm.lMap swap X) (Semiterm.lMap swap U) (Semiterm.lMap swap W)) := by
  rw [eval_swappedReading, lMap_swap_qDG, ← stdReadingV_eq_stdReading]


end fixedFormulas

/-! ### 5. The instance equations on codes, in every model -/

section instanceEq

/-- The six codes of the substituted terms of `qDG X U W`, as an internal vector. -/
noncomputable def qDGVec (X : Semiterm LAct Empty 1) (U W : ClosedSemiterm LAct 0) : V :=
  (⌜(Rew.emb TDi : SyntacticSemiterm LAct 1)⌝ : V) ∷
    ⌜(Rew.emb (cl uDi : Semiterm LAct Empty 1) : SyntacticSemiterm LAct 1)⌝ ∷
    ⌜(Rew.emb (cl wDi : Semiterm LAct Empty 1) : SyntacticSemiterm LAct 1)⌝ ∷
    ⌜(Rew.emb X : SyntacticSemiterm LAct 1)⌝ ∷
    ⌜(Rew.emb (cl U : Semiterm LAct Empty 1) : SyntacticSemiterm LAct 1)⌝ ∷
    ⌜(Rew.emb (cl W : Semiterm LAct Empty 1) : SyntacticSemiterm LAct 1)⌝ ∷ 0


/-- The code of `qDG X U W` is the internal substitution of `qDGVec X U W` into the template code. -/
theorem quote_qDG (X : Semiterm LAct Empty 1) (U W : ClosedSemiterm LAct 0) :
    (⌜qDG X U W⌝ : V) = subst LAct (qDGVec X U W) (⌜templateD⌝ : V) := by
  unfold qDG
  rw [Sentence.quote_def, Semiformula.coe_subst_eq_subst_coe, Semiformula.quote_def,
    Semiformula.typed_quote_substs, Bootstrapping.Semiformula.val_substs, ← Semiformula.quote_def,
    ← Sentence.quote_def]
  congr 1

lemma qDGVec_semitermVec (X : Semiterm LAct Empty 1) (U W : ClosedSemiterm LAct 0) :
    IsSemitermVec LAct 6 1 (qDGVec X U W : V) := by
  rw [six_eq, qDGVec]
  exact ((((((IsSemitermVec.nil 1).adjoin (semiterm_quote_emb₁ _)).adjoin (semiterm_quote_emb₁ _)).adjoin
    (semiterm_quote_emb₁ _)).adjoin (semiterm_quote_emb₁ _)).adjoin (semiterm_quote_emb₁ _)).adjoin
    (semiterm_quote_emb₁ _)

/-- Substituting `binNumeral k` into the six codes gives the description vector of `(DimcidV k, opp)`,
given that the opponent's triple describes `opp` on codes. -/
theorem termSubstVec_qDGVec (k : V) (X : Semiterm LAct Empty 1) (U W : ClosedSemiterm LAct 0) {opp : V}
    (hX : termSubst LAct (binNumeral k ∷ (0 : V)) (⌜(Rew.emb X : SyntacticSemiterm LAct 1)⌝ : V) = codeTerm (canonical opp))
    (hU : (⌜U⌝ : V) = revalueU opp) (hW : (⌜W⌝ : V) = revalueW opp) :
    termSubstVec LAct 6 (binNumeral k ∷ (0 : V)) (qDGVec X U W) = descriptions (DimcidV k) opp := by
  have hT : IsUTerm LAct (⌜(Rew.emb TDi : SyntacticSemiterm LAct 1)⌝ : V) := (semiterm_quote_emb₁ _).isUTerm
  have hU' : IsUTerm LAct (⌜(Rew.emb (cl uDi : Semiterm LAct Empty 1) : SyntacticSemiterm LAct 1)⌝ : V) :=
    (semiterm_quote_emb₁ _).isUTerm
  have hW' : IsUTerm LAct (⌜(Rew.emb (cl wDi : Semiterm LAct Empty 1) : SyntacticSemiterm LAct 1)⌝ : V) :=
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
  have sT : termSubst LAct (binNumeral k ∷ 0) (⌜(Rew.emb TDi : SyntacticSemiterm LAct 1)⌝ : V) =
      codeTerm (canonical (DimcidV k)) := by
    rw [quote_emb_TDi, termSubst_tower, canonical_DimcidV]
  have sU : termSubst LAct (binNumeral k ∷ 0) (⌜(Rew.emb (cl uDi : Semiterm LAct Empty 1) : SyntacticSemiterm LAct 1)⌝ : V) =
      revalueU (DimcidV k) := by
    rw [quote_emb_cl_V, termSubst_closed _ (semiterm_quote_emb₀ _), revalueU_DimcidV, Semiterm.empty_quote_def]
  have sW : termSubst LAct (binNumeral k ∷ 0) (⌜(Rew.emb (cl wDi : Semiterm LAct Empty 1) : SyntacticSemiterm LAct 1)⌝ : V) =
      revalueW (DimcidV k) := by
    rw [quote_emb_cl_V, termSubst_closed _ (semiterm_quote_emb₀ _), revalueW_DimcidV, Semiterm.empty_quote_def]
  have sU2 : termSubst LAct (binNumeral k ∷ 0) (⌜(Rew.emb (cl U : Semiterm LAct Empty 1) : SyntacticSemiterm LAct 1)⌝ : V) =
      revalueU opp := by
    rw [quote_emb_cl_V, termSubst_closed _ (semiterm_quote_emb₀ _), ← Semiterm.empty_quote_def, hU]
  have sW2 : termSubst LAct (binNumeral k ∷ 0) (⌜(Rew.emb (cl W : Semiterm LAct Empty 1) : SyntacticSemiterm LAct 1)⌝ : V) =
      revalueW opp := by
    rw [quote_emb_cl_V, termSubst_closed _ (semiterm_quote_emb₀ _), ← Semiterm.empty_quote_def, hW]
  unfold qDGVec descriptions
  rw [six_eq, termSubstVec_cons hT e5, termSubstVec_cons hU' e4, termSubstVec_cons hW' e3,
    termSubstVec_cons hX' e2, termSubstVec_cons hU'' e1, termSubstVec_cons hW'' e0, termSubstVec_nil,
    sT, sU, sW, hX, sU2, sW2]

/-- **DIMCID's instance equation on codes, in every model**: the guard code of `DimcidV k` against
`opp` is the `binNumeral k`-instance of `⌜qDG X U W⌝` whenever `(X, U, W)` describes `opp` on codes. -/
theorem guardCode_DimcidV_eq_instB (k : V) (X : Semiterm LAct Empty 1) (U W : ClosedSemiterm LAct 0) {opp : V}
    (hX : termSubst LAct (binNumeral k ∷ (0 : V)) (⌜(Rew.emb X : SyntacticSemiterm LAct 1)⌝ : V) = codeTerm (canonical opp))
    (hU : (⌜U⌝ : V) = revalueU opp) (hW : (⌜W⌝ : V) = revalueW opp) :
    guardCode (⌜templateD⌝ : V) (DimcidV k) opp = instB (⌜qDG X U W⌝ : V) k := by
  show guardCode (⌜templateD⌝ : V) (DimcidV k) opp = subst LAct (binNumeral k ∷ (0 : V)) (⌜qDG X U W⌝ : V)
  rw [quote_qDG, substs_substs (p := (⌜templateD⌝ : V)) (l := 6)
    (by simpa using Sentence.quote_isSemiformula (V := V) templateD)
    (binNumeral_cons_semitermVec k) (qDGVec_semitermVec X U W), termSubstVec_qDGVec k X U W hX hU hW]
  rfl

/-- The transposed searcher's guard code against `transposeCode opp` is the code-level τ of DIMCID's
against `opp`. -/
lemma guardCode_DimcidTV_eq_revalue (k opp : V) :
    guardCode (⌜templateDT⌝ : V) (DimcidTV k) (transposeCode opp) =
      revalueTemplate 1 0 (guardCode (⌜templateD⌝ : V) (DimcidV k) opp) := by
  have hg0 : IsSemiformula LAct 6 (⌜templateD⌝ : V) := by
    simpa using Sentence.quote_isSemiformula (V := V) templateD
  have hg1 : IsSemiformula LAct 6 (⌜templateDT⌝ : V) := by
    simpa using Sentence.quote_isSemiformula (V := V) templateDT
  rw [← substTemplate_of_template hg0, revalueTemplate_substTemplate, transposeCode_DimcidV, revalueTemplate_quote_sentence₆_V,
    lMap_swap_templateD, substTemplate_of_template hg1]

/-- **The transposed searcher's instance equation on codes, in every model.** -/
theorem guardCode_DimcidTV_eq_instB (k : V) (X : Semiterm LAct Empty 1) (U W : ClosedSemiterm LAct 0) {opp : V}
    (hX : termSubst LAct (binNumeral k ∷ (0 : V)) (⌜(Rew.emb X : SyntacticSemiterm LAct 1)⌝ : V) = codeTerm (canonical opp))
    (hU : (⌜U⌝ : V) = revalueU opp) (hW : (⌜W⌝ : V) = revalueW opp) :
    guardCode (⌜templateDT⌝ : V) (DimcidTV k) (transposeCode opp) =
      instB (⌜qTG (Semiterm.lMap swap X) (Semiterm.lMap swap U) (Semiterm.lMap swap W)⌝ : V) k := by
  rw [guardCode_DimcidTV_eq_revalue, guardCode_DimcidV_eq_instB k X U W hX hU hW]
  unfold instB
  rw [revalueTemplate_subst isAct_one isAct_zero (Sentence.quote_isSemiformul₁ (qDG X U W))
    (binNumeral_cons_semitermVec k), revalueTemplate_quote_sentence_V, lMap_swap_qDG]
  congr 1
  rw [show (1 : V) = 0 + 1 by simp, termRelabelVec_cons (binNumeral_term_LAct k).isUTerm IsUTermVec.empty,
    termRelabelVec_nil, termRelabel_binNumeral]

/-! #### The search clauses -/

/-- **DIMCID's search clause in every model** (fuel `2`): a proof of its guard within the budget
makes `DimcidV k` DEFECT (`pConst 1`). -/
theorem dimcid_search_V (k opp : V) :
    LenBox TAct k (guardCode (⌜templateD⌝ : V) (DimcidV k) opp) →
      EvalGraph 2 (DimcidV k) opp (DimcidV k) 1 := by
  intro h
  rw [show (2 : V) = 1 + 1 from one_add_one_eq_two.symm]
  show EvalGraph (1 + 1) (DimcidV k) opp (pSearch k (⌜templateD⌝ : V) (pConst 1) (pConst 0)) 1
  rw [EvalGraph.search_iff₆ (isSemiformula_quote₆ templateD)]
  left
  refine ⟨h, ?_⟩
  have e : EvalGraph (0 + 1) (DimcidV k) opp (pConst 1) 1 := EvalGraph.const_iff.mpr rfl
  rwa [zero_add] at e

/-- **The transposed searcher's search clause in every model** (fuel `2`): found ⇒ `C`. -/
theorem dimcidT_search_V (k opp : V) :
    LenBox TAct k (guardCode (⌜templateDT⌝ : V) (DimcidTV k) opp) →
      EvalGraph 2 (DimcidTV k) opp (DimcidTV k) 0 := by
  intro h
  rw [show (2 : V) = 1 + 1 from one_add_one_eq_two.symm]
  show EvalGraph (1 + 1) (DimcidTV k) opp (pSearch k (⌜templateDT⌝ : V) (pConst 0) (pConst 1)) 0
  rw [EvalGraph.search_iff₆ (isSemiformula_quote₆ templateDT)]
  left
  refine ⟨h, ?_⟩
  rw [show (1 : V) = 0 + 1 by simp, EvalGraph.const_iff]

end instanceEq

/-! ### 6. The conjunction family, generic in the opponent -/

section conj

/-- **The Löb family of a DIMCID cell**: DIMCID's guard against `(X, U, W)` AND the transposed
searcher's guard against the transposed triple. -/
noncomputable def pG (X : Semiterm LAct Empty 1) (U W : ClosedSemiterm LAct 0) : Semisentence LAct 1 :=
  qDG X U W ⋏ qTG (Semiterm.lMap swap X) (Semiterm.lMap swap U) (Semiterm.lMap swap W)

lemma pG_def (X : Semiterm LAct Empty 1) (U W : ClosedSemiterm LAct 0) :
    pG X U W = qDG X U W ⋏ qTG (Semiterm.lMap swap X) (Semiterm.lMap swap U) (Semiterm.lMap swap W) := rfl

lemma lMap_swap_pG (X : Semiterm LAct Empty 1) (U W : ClosedSemiterm LAct 0) :
    Semiformula.lMap swap (pG X U W) =
      qTG (Semiterm.lMap swap X) (Semiterm.lMap swap U) (Semiterm.lMap swap W) ⋏ qDG X U W := by
  rw [pG_def, LogicalConnective.HomClass.map_and, lMap_swap_qDG, lMap_swap_qTG, term_lMap_swap_swap,
    term_lMap_swap_swap, term_lMap_swap_swap]

/-- **`instB ⌜pG X U W⌝ k` is the conjunction of the two instances.** -/
theorem instB_quote_pG (X : Semiterm LAct Empty 1) (U W : ClosedSemiterm LAct 0) (k : V) :
    instB (⌜pG X U W⌝ : V) k =
      instB (⌜qDG X U W⌝ : V) k ^⋏
        instB (⌜qTG (Semiterm.lMap swap X) (Semiterm.lMap swap U) (Semiterm.lMap swap W)⌝ : V) k :=
  instB_quote_and _ _ k

lemma formulaLen_instB_pG (X : Semiterm LAct Empty 1) (U W : ClosedSemiterm LAct 0) (k : V) :
    formulaLen LAct (instB (⌜pG X U W⌝ : V) k) =
      formulaLen LAct (instB (⌜qDG X U W⌝ : V) k) +
        formulaLen LAct (instB (⌜qTG (Semiterm.lMap swap X) (Semiterm.lMap swap U) (Semiterm.lMap swap W)⌝ : V) k)
        + 1 := by
  rw [instB_quote_pG,
    formulaLen_and (isFormula_instB_quote _ k).isUFormula (isFormula_instB_quote _ k).isUFormula]

/-- **Both searchers find their guards from a box of the conjunction**: for every budget `a` with
`a + 8(|qDG(k)| + |qTG(k)|) + 7 ≤ k`, a `TAct`-proof code of the `k`-instance of `pG` of length
`≤ a` makes `DimcidV k` defect against `opp` and `DimcidTV k` cooperate with `transposeCode opp`
(fuel 2), given the code-level description hypotheses. -/
theorem pG_both_V (k : V) (X : Semiterm LAct Empty 1) (U W : ClosedSemiterm LAct 0) {opp : V}
    (hX : termSubst LAct (binNumeral k ∷ (0 : V)) (⌜(Rew.emb X : SyntacticSemiterm LAct 1)⌝ : V) = codeTerm (canonical opp))
    (hU : (⌜U⌝ : V) = revalueU opp) (hW : (⌜W⌝ : V) = revalueW opp) : ∀ a : V,
    a + 8 * (formulaLen LAct (instB (⌜qDG X U W⌝ : V) k) +
      formulaLen LAct (instB (⌜qTG (Semiterm.lMap swap X) (Semiterm.lMap swap U) (Semiterm.lMap swap W)⌝ : V) k))
      + 7 ≤ k →
    LenBoxUnbounded TAct a (instB (⌜pG X U W⌝ : V) k) →
    EvalGraph 2 (DimcidV k) opp (DimcidV k) 1 ∧ EvalGraph 2 (DimcidTV k) (transposeCode opp) (DimcidTV k) 0 := by
  intro a ha h
  rw [instB_quote_pG] at h
  have hx := isFormula_instB_quote (qDG X U W) k
  have hy := isFormula_instB_quote (qTG (Semiterm.lMap swap X) (Semiterm.lMap swap U) (Semiterm.lMap swap W)) k
  have h₁ := lenBoxUnbounded_mono_V ha (lenBoxUnbounded_andL_V hx hy h)
  have h₂ := lenBoxUnbounded_mono_V ha (lenBoxUnbounded_andR_V hx hy h)
  rw [lenBoxUnbounded_iff_lenBox, ← guardCode_DimcidV_eq_instB k X U W hX hU hW] at h₁
  rw [lenBoxUnbounded_iff_lenBox, ← guardCode_DimcidTV_eq_instB k X U W hX hU hW] at h₂
  exact ⟨dimcid_search_V k opp h₁, dimcidT_search_V k _ h₂⟩

/-- **Both searchers FIND their guards** (the box form of `pG_both_V`). -/
theorem pG_guards_V (k : V) (X : Semiterm LAct Empty 1) (U W : ClosedSemiterm LAct 0) {opp : V}
    (hX : termSubst LAct (binNumeral k ∷ (0 : V)) (⌜(Rew.emb X : SyntacticSemiterm LAct 1)⌝ : V) = codeTerm (canonical opp))
    (hU : (⌜U⌝ : V) = revalueU opp) (hW : (⌜W⌝ : V) = revalueW opp) (a : V)
    (ha : a + 8 * (formulaLen LAct (instB (⌜qDG X U W⌝ : V) k) +
      formulaLen LAct (instB (⌜qTG (Semiterm.lMap swap X) (Semiterm.lMap swap U) (Semiterm.lMap swap W)⌝ : V) k))
      + 7 ≤ k)
    (hpc : LenBoxUnbounded TAct a (instB (⌜pG X U W⌝ : V) k)) :
    LenBox TAct k (guardCode (⌜templateD⌝ : V) (DimcidV k) opp) ∧
    LenBox TAct k (guardCode (⌜templateDT⌝ : V) (DimcidTV k) (transposeCode opp)) := by
  rw [instB_quote_pG] at hpc
  have hx := isFormula_instB_quote (qDG X U W) k
  have hy := isFormula_instB_quote (qTG (Semiterm.lMap swap X) (Semiterm.lMap swap U) (Semiterm.lMap swap W)) k
  have h₁ := lenBoxUnbounded_mono_V ha (lenBoxUnbounded_andL_V hx hy hpc)
  have h₂ := lenBoxUnbounded_mono_V ha (lenBoxUnbounded_andR_V hx hy hpc)
  rw [lenBoxUnbounded_iff_lenBox, ← guardCode_DimcidV_eq_instB k X U W hX hU hW] at h₁
  rw [lenBoxUnbounded_iff_lenBox, ← guardCode_DimcidTV_eq_instB k X U W hX hU hW] at h₂
  exact ⟨h₁, h₂⟩

/-! #### `pG` in both readings -/

/-- `pG(k)` in the standard reading, given that the triple describes `opp` and the transposed
triple describes `opp'` (in every intended instance, `opp' = transposeCode opp`). -/
theorem eval_pG_iff_std (k : V) (X : Semiterm LAct Empty 1) (U W : ClosedSemiterm LAct 0) {opp opp' : V}
    (hopp : revalue (U.val (s := stdReadingV V) ![] Empty.elim) (W.val (s := stdReadingV V) ![] Empty.elim)
      (X.val (s := stdReadingV V) ![k] Empty.elim) = opp)
    (hopp' : revalue ((Semiterm.lMap swap U).val (s := stdReadingV V) ![] Empty.elim)
      ((Semiterm.lMap swap W).val (s := stdReadingV V) ![] Empty.elim)
      ((Semiterm.lMap swap X).val (s := stdReadingV V) ![k] Empty.elim) = opp') :
    Semiformula.Eval (s := stdReadingV V) ![k] Empty.elim (pG X U W) ↔
      ((∃ n, EvalGraph n (DimcidV k) opp (DimcidV k) 0) → (∃ n, EvalGraph n opp (DimcidV k) opp 1)) ∧
      ((∃ n, EvalGraph n (DimcidTV k) opp' (DimcidTV k) 1) → (∃ n, EvalGraph n opp' (DimcidTV k) opp' 0)) := by
  rw [pG_def]
  simp only [LogicalConnective.HomClass.map_and, LogicalConnective.Prop.and_eq]
  rw [eval_qDG_iff_V k X U W hopp, eval_qTG_iff_V k _ _ _ hopp']

/-- `pG(k)` in the swapped reading: the SAME content (the conjuncts exchange roles). -/
theorem eval_pG_iff_swap (k : V) (X : Semiterm LAct Empty 1) (U W : ClosedSemiterm LAct 0) {opp opp' : V}
    (hopp : revalue (U.val (s := stdReadingV V) ![] Empty.elim) (W.val (s := stdReadingV V) ![] Empty.elim)
      (X.val (s := stdReadingV V) ![k] Empty.elim) = opp)
    (hopp' : revalue ((Semiterm.lMap swap U).val (s := stdReadingV V) ![] Empty.elim)
      ((Semiterm.lMap swap W).val (s := stdReadingV V) ![] Empty.elim)
      ((Semiterm.lMap swap X).val (s := stdReadingV V) ![k] Empty.elim) = opp') :
    Semiformula.Eval (s := swappedReading V) ![k] Empty.elim (pG X U W) ↔
      ((∃ n, EvalGraph n (DimcidV k) opp (DimcidV k) 0) → (∃ n, EvalGraph n opp (DimcidV k) opp 1)) ∧
      ((∃ n, EvalGraph n (DimcidTV k) opp' (DimcidTV k) 1) → (∃ n, EvalGraph n opp' (DimcidTV k) opp' 0)) := by
  rw [eval_swappedReading, lMap_swap_pG, ← stdReadingV_eq_stdReading]
  simp only [LogicalConnective.HomClass.map_and, LogicalConnective.Prop.and_eq]
  rw [eval_qDG_iff_V k X U W hopp, eval_qTG_iff_V k _ _ _ hopp', and_comm]

/-- `pG(k)` in the standard reading, `stdReading` form. -/
theorem eval_pG_iff_stdReading (k : V) (X : Semiterm LAct Empty 1) (U W : ClosedSemiterm LAct 0) {opp opp' : V}
    (hopp : revalue (U.val (s := stdReadingV V) ![] Empty.elim) (W.val (s := stdReadingV V) ![] Empty.elim)
      (X.val (s := stdReadingV V) ![k] Empty.elim) = opp)
    (hopp' : revalue ((Semiterm.lMap swap U).val (s := stdReadingV V) ![] Empty.elim)
      ((Semiterm.lMap swap W).val (s := stdReadingV V) ![] Empty.elim)
      ((Semiterm.lMap swap X).val (s := stdReadingV V) ![k] Empty.elim) = opp') :
    Semiformula.Eval (s := stdReading V) ![k] Empty.elim (pG X U W) ↔
      ((∃ n, EvalGraph n (DimcidV k) opp (DimcidV k) 0) → (∃ n, EvalGraph n opp (DimcidV k) opp 1)) ∧
      ((∃ n, EvalGraph n (DimcidTV k) opp' (DimcidTV k) 1) → (∃ n, EvalGraph n opp' (DimcidTV k) opp' 0)) := by
  rw [← stdReadingV_eq_stdReading]; exact eval_pG_iff_std k X U W hopp hopp'

/-! #### The Löb premise against ANY described opponent (the self-fulfilling refutation) -/

/-- **DIMCID's Löb premise against ANY described opponent, slack `(7, 8)`** (`loebSound_pDi0`, made
generic): a box of the family makes `DimcidV k` defect against the opponent and the transposed searcher
cooperate with the transposed opponent, so the antecedents "I play C" / "I play D" are FALSE and both
implications hold in both readings — whatever the consequents say. This is the self-fulfilling refutation:
the guard "I cooperate ⇒ …" is made true by the defection its own proof triggers. -/
theorem loebSound_pG_of {X : Semiterm LAct Empty 1} {U W : ClosedSemiterm LAct 0} (h : Describes X U W) :
    LoebSound (pG X U W) 7 8 := by
  intro V _ _ k a ha hp
  have : V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁ := inferInstance
  have ha' : a + 8 * (formulaLen LAct (instB (⌜qDG X U W⌝ : V) k) +
      formulaLen LAct (instB (⌜qTG (Semiterm.lMap swap X) (Semiterm.lMap swap U) (Semiterm.lMap swap W)⌝ : V) k))
      + 7 ≤ k :=
    le_trans (pConj_slack_le a _ _ _ (formulaLen_instB_pG X U W k)) ha
  obtain ⟨h1, h2⟩ := pG_both_V k X U W (h.hX V k) (h.hU V k) (h.hW V k) a ha' hp
  have hA : ¬ ∃ n, EvalGraph n (DimcidV k) (descVal X U W k) (DimcidV k) 0 := by
    rintro ⟨n, hn⟩
    exact _root_.zero_ne_one (EvalGraph.unique_V' n 2 _ _ _ _ _ hn h1)
  have hB : ¬ ∃ n, EvalGraph n (DimcidTV k) (transposeCode (descVal X U W k)) (DimcidTV k) 1 := by
    rintro ⟨n, hn⟩
    exact _root_.one_ne_zero (EvalGraph.unique_V' n 2 _ _ _ _ _ hn h2)
  exact ⟨(eval_pG_iff_stdReading k X U W rfl (h.hT V k)).mpr ⟨fun h ↦ absurd h hA, fun h ↦ absurd h hB⟩,
    (eval_pG_iff_swap k X U W rfl (h.hT V k)).mpr ⟨fun h ↦ absurd h hA, fun h ↦ absurd h hB⟩⟩

/-- **DIMCID's Löb premise against an opponent described above `K`, slack `(7 + K, 8)`**
(`loebSound_pG_of`, with the threshold supplied by the slack as in `loebSound_pPM`). -/
theorem loebSound_pG_of_above {K : ℕ} {X : Semiterm LAct Empty 1} {U W : ClosedSemiterm LAct 0}
    (h : DescribesAbove K X U W) : LoebSound (pG X U W) (7 + K) 8 := by
  intro V _ _ k a ha hp
  have : V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁ := inferInstance
  have hk : (K : V) ≤ k :=
    le_trans (Nat.cast_le.mpr (Nat.le_add_left K 7)) (le_trans le_add_self (le_trans le_self_add ha))
  have h7 : ((7 : ℕ) : V) ≤ ((7 + K : ℕ) : V) := Nat.cast_le.mpr (Nat.le_add_right 7 K)
  have hb : a + ((7 : ℕ) : V) + ((8 : ℕ) : V) * formulaLen LAct (instB (⌜pG X U W⌝ : V) k) ≤
      a + ((7 + K : ℕ) : V) + ((8 : ℕ) : V) * formulaLen LAct (instB (⌜pG X U W⌝ : V) k) :=
    _root_.add_le_add_left (_root_.add_le_add_right h7 a) _
  have ha' : a + 8 * (formulaLen LAct (instB (⌜qDG X U W⌝ : V) k) +
      formulaLen LAct (instB (⌜qTG (Semiterm.lMap swap X) (Semiterm.lMap swap U) (Semiterm.lMap swap W)⌝ : V) k))
      + 7 ≤ k :=
    le_trans (pConj_slack_le a _ _ _ (formulaLen_instB_pG X U W k)) (le_trans hb ha)
  obtain ⟨h1, h2⟩ := pG_both_V k X U W (h.hX V k hk) (h.hU V k hk) (h.hW V k hk) a ha' hp
  have hA : ¬ ∃ n, EvalGraph n (DimcidV k) (descVal X U W k) (DimcidV k) 0 := by
    rintro ⟨n, hn⟩
    exact _root_.zero_ne_one (EvalGraph.unique_V' n 2 _ _ _ _ _ hn h1)
  have hB : ¬ ∃ n, EvalGraph n (DimcidTV k) (transposeCode (descVal X U W k)) (DimcidTV k) 1 := by
    rintro ⟨n, hn⟩
    exact _root_.one_ne_zero (EvalGraph.unique_V' n 2 _ _ _ _ _ hn h2)
  exact ⟨(eval_pG_iff_stdReading k X U W rfl (h.hT V k hk)).mpr ⟨fun h ↦ absurd h hA, fun h ↦ absurd h hB⟩,
    (eval_pG_iff_swap k X U W rfl (h.hT V k hk)).mpr ⟨fun h ↦ absurd h hA, fun h ↦ absurd h hB⟩⟩

end conj

/-! ### 7. Cell 1 — DIMCID × DIMCID `(D, D)` -/

section selfCell

/-- DIMCID's own triple describes `DimcidV k` on codes: the `X`-hypothesis. -/
lemma hX_dimcid (k : V) :
    termSubst LAct (binNumeral k ∷ (0 : V)) (⌜(Rew.emb TDi : SyntacticSemiterm LAct 1)⌝ : V) =
      codeTerm (canonical (DimcidV k)) := by
  rw [quote_emb_TDi, termSubst_tower, canonical_DimcidV]

lemma hU_dimcid (k : V) : (⌜uDi⌝ : V) = revalueU (DimcidV k) := (revalueU_DimcidV k).symm
lemma hW_dimcid (k : V) : (⌜wDi⌝ : V) = revalueW (DimcidV k) := (revalueW_DimcidV k).symm

/-- DIMCID's own triple describes `DimcidV k` in `stdReadingV V`. -/
lemma desc_dimcid (k : V) :
    revalue (uDi.val (s := stdReadingV V) ![] Empty.elim) (wDi.val (s := stdReadingV V) ![] Empty.elim)
      (TDi.val (s := stdReadingV V) ![k] Empty.elim) = DimcidV k := by
  rw [val_TDi_V]; exact revalue_val_uDi_wDi_V k

/-- The transposed triple describes `DimcidTV k` in `stdReadingV V`. -/
lemma descT_dimcid (k : V) :
    revalue ((Semiterm.lMap swap uDi).val (s := stdReadingV V) ![] Empty.elim)
      ((Semiterm.lMap swap wDi).val (s := stdReadingV V) ![] Empty.elim)
      ((Semiterm.lMap swap TDi).val (s := stdReadingV V) ![k] Empty.elim) = DimcidTV k := by
  rw [lMap_swap_TDi, val_TDi_V]; exact revalue_val_uDiT_wDiT_V k


/-- **The Löb family of the self-play cell**: `pDD := qDD ⋏ (its transposition)`. -/
noncomputable def pDD : Semisentence LAct 1 := pG TDi uDi wDi

lemma pDD_def : pDD = pG TDi uDi wDi := rfl

/-- **DIMCID's canonical triple describes `DimcidV k` in every model** (`hX/hU/hW_dimcid`, `hopp/descT_dimcid`,
packaged as a `Describes`; consolidation stage 5). -/
theorem describes_dimcid : Describes TDi uDi wDi where
  hX := by intro V _ _ k; rw [descVal_def, desc_dimcid]; exact hX_dimcid k
  hU := by intro V _ _ k; rw [descVal_def, desc_dimcid]; exact hU_dimcid k
  hW := by intro V _ _ k; rw [descVal_def, desc_dimcid]; exact hW_dimcid k
  hT := by intro V _ _ k; rw [descVal_def, descVal_def, descT_dimcid, desc_dimcid, transposeCode_DimcidV]

/-- **The bounded Löb premise of the self-play family, slack `(7, 8)`**: a proof code of `pDD(k)` of
length `a` with `a + 7 + 8·|pDD(k)| ≤ k` makes both searchers find their guards, so `DimcidV k`
defects and `DimcidTV k` cooperates (fuel 2), which makes both implications TRUE (their
consequents hold) in both readings. -/
theorem loebSound_pDD : LoebSound pDD 7 8 := by
  rw [pDD_def]; exact loebSound_pG_of describes_dimcid

/-- **The self-play cell, packaged**: for all large `k`, both searchers find their guards against
themselves (fuel 2) and both guard boxes hold — `family_found pDD` (the arithmetized `pblt_engine`)
then ∧-elimination on codes. -/
theorem loeb_Dimcid_vs_Dimcid_core_of_nec {d : ℕ} (hE : BoundedInnerNec d) :
    ∃ k₀ : ℕ, ∀ k : ℕ, k₀ < k →
      (EvalGraph 2 (Dimcid k) (Dimcid k) (Dimcid k) 1 ∧
        EvalGraph 2 (DimcidTV (V := ℕ) k) (DimcidTV k) (DimcidTV k) 0) ∧
      (LenBox TAct k (guardCode (⌜templateD⌝ : ℕ) (Dimcid k) (Dimcid k)) ∧
        LenBox TAct k (guardCode (⌜templateDT⌝ : ℕ) (DimcidTV (V := ℕ) k) (DimcidTV k))) := by
  obtain ⟨k₀, h⟩ := family_found pDD hE loebSound_pDD
  refine ⟨k₀, fun k hk ↦ ?_⟩
  obtain ⟨a, ha, hpc⟩ := h k hk
  have ha' := le_def.mpr (pConj_slack_nat a _ _ _ k (formulaLen_instB_pG (V := ℕ) TDi uDi wDi k) ha)
  have h1 := pG_both_V (V := ℕ) k TDi uDi wDi (hX_dimcid k) (hU_dimcid k) (hW_dimcid k) a ha' hpc
  have h2 := pG_guards_V (V := ℕ) k TDi uDi wDi (hX_dimcid k) (hU_dimcid k) (hW_dimcid k) a ha' hpc
  rw [transposeCode_DimcidV] at h1 h2
  exact ⟨h1, h2⟩

/-- **DIMCID × DIMCID is `(D, D)` in PA-`S'`, conditional on bounded inner necessitation**: for all
large `k`, `Dimcid k` defects against itself (fuel 2). -/
theorem loeb_Dimcid_vs_Dimcid_of_nec {d : ℕ} (hE : BoundedInnerNec d) :
    ∃ k₀ : ℕ, ∀ k : ℕ, k₀ < k → EvalGraph 2 (Dimcid k) (Dimcid k) (Dimcid k) 1 := by
  obtain ⟨k₀, h⟩ := loeb_Dimcid_vs_Dimcid_core_of_nec hE
  exact ⟨k₀, fun k hk ↦ (h k hk).1.1⟩


/-- **DIMCID × DIMCID `(D, D)` in PA-`S'`, unconditional**: for all large `k`, `Dimcid k` defects
against itself. -/
theorem loeb_Dimcid_vs_Dimcid :
    ∃ k₀ : ℕ, ∀ k : ℕ, k₀ < k → EvalGraph 2 (Dimcid k) (Dimcid k) (Dimcid k) 1 :=
  loeb_Dimcid_vs_Dimcid_of_nec boundedInnerNec_sixteen


end selfCell

/-! ### 8. Cell 2 — DIMCID × Mirror `(D, D)` -/

section mirrorCell


/-- Mirror's closed triple describes `MirrorV` on codes: the `X`-hypothesis. -/
lemma hX_mirror (k : V) :
    termSubst LAct (binNumeral k ∷ (0 : V))
      (⌜(Rew.emb (cl TM : Semiterm LAct Empty 1) : SyntacticSemiterm LAct 1)⌝ : V) = codeTerm (canonical MirrorV) := by
  rw [quote_emb_cl_V, termSubst_closed _ (semiterm_quote_emb₀ _), quote_emb_TM, canonical_MirrorV]

lemma hU_mirror : (⌜numT 0⌝ : V) = revalueU MirrorV := by
  rw [Semiterm.empty_quote_def, quote_emb_numT, revalueU_MirrorV, Nat.cast_zero]

lemma hW_mirror : (⌜numT 1⌝ : V) = revalueW MirrorV := by
  rw [Semiterm.empty_quote_def, quote_emb_numT, revalueW_MirrorV, Nat.cast_one]

/-- Mirror's closed triple describes `MirrorV` in `stdReadingV V`. -/
lemma desc_mirror (k : V) :
    revalue ((numT 0).val (s := stdReadingV V) ![] Empty.elim) ((numT 1).val (s := stdReadingV V) ![] Empty.elim)
      ((cl TM : Semiterm LAct Empty 1).val (s := stdReadingV V) ![k] Empty.elim) = MirrorV := by
  rw [val_numT_V, val_numT_V, Nat.cast_zero, Nat.cast_one, val_cl_V, val_TM_V, revalue_zero_one]

/-- The transposed triple still describes `MirrorV` (Mirror is τ-fixed). -/
lemma descT_mirror (k : V) :
    revalue ((Semiterm.lMap swap (numT 0)).val (s := stdReadingV V) ![] Empty.elim)
      ((Semiterm.lMap swap (numT 1)).val (s := stdReadingV V) ![] Empty.elim)
      ((Semiterm.lMap swap (cl TM : Semiterm LAct Empty 1)).val (s := stdReadingV V) ![k] Empty.elim) = MirrorV := by
  rw [lMap_swap_numT, lMap_swap_numT, lMap_swap_cl, lMap_swap_TM]
  exact desc_mirror k


/-- **The Löb family of the Mirror cell**: `pDMi := qDMi ⋏ (its transposition)`. -/
noncomputable def pDMi : Semisentence LAct 1 := pG (cl TM) (numT 0) (numT 1)

lemma pDMi_def : pDMi = pG (cl TM) (numT 0) (numT 1) := rfl

/-- **Mirror's closed triple `(cl TM, 0, 1)` describes `MirrorV` in every model** (`hX/hU/hW_mirror`,
`hopp/descT_mirror`, packaged; consolidation stage 5). -/
theorem describes_mirror : Describes (cl TM) (numT 0) (numT 1) where
  hX := by intro V _ _ k; rw [descVal_def, desc_mirror]; exact hX_mirror k
  hU := by intro V _ _ k; rw [descVal_def, desc_mirror]; exact hU_mirror
  hW := by intro V _ _ k; rw [descVal_def, desc_mirror]; exact hW_mirror
  hT := by intro V _ _ k; rw [descVal_def, descVal_def, descT_mirror, desc_mirror, transposeCode_MirrorV]

/-- **The bounded Löb premise of the Mirror family, slack `(7, 8)`**: a box of `pDMi(k)` makes both
searchers find their guards against Mirror, `DimcidV k` defects and `DimcidTV k` cooperates
(fuel 2), Mirror COPIES (fuel 3), so both implications are true in both readings. -/
theorem loebSound_pDMi : LoebSound pDMi 7 8 := by
  rw [pDMi_def]; exact loebSound_pG_of describes_mirror

/-- **The Mirror cell, packaged**: for all large `k`, both searchers find their guards against
Mirror (fuel 2) and both guard boxes hold. -/
theorem loeb_Dimcid_vs_Mirror_core_of_nec {d : ℕ} (hE : BoundedInnerNec d) :
    ∃ k₀ : ℕ, ∀ k : ℕ, k₀ < k →
      (EvalGraph 2 (Dimcid k) Mirror (Dimcid k) 1 ∧ EvalGraph 2 (DimcidTV (V := ℕ) k) Mirror (DimcidTV k) 0) ∧
      (LenBox TAct k (guardCode (⌜templateD⌝ : ℕ) (Dimcid k) Mirror) ∧
        LenBox TAct k (guardCode (⌜templateDT⌝ : ℕ) (DimcidTV (V := ℕ) k) Mirror)) := by
  obtain ⟨k₀, h⟩ := family_found pDMi hE loebSound_pDMi
  refine ⟨k₀, fun k hk ↦ ?_⟩
  obtain ⟨a, ha, hpc⟩ := h k hk
  have ha' := le_def.mpr (pConj_slack_nat a _ _ _ k (formulaLen_instB_pG (V := ℕ) (cl TM) (numT 0) (numT 1) k) ha)
  have h1 := pG_both_V (V := ℕ) k (cl TM) (numT 0) (numT 1) (hX_mirror k) hU_mirror hW_mirror a ha' hpc
  have h2 := pG_guards_V (V := ℕ) k (cl TM) (numT 0) (numT 1) (hX_mirror k) hU_mirror hW_mirror a ha' hpc
  rw [transposeCode_MirrorV] at h1 h2
  exact ⟨h1, h2⟩

/-- **DIMCID × Mirror is `(D, D)` in PA-`S'`, conditional on bounded inner necessitation**: for all
large `k`, `Dimcid k` defects against Mirror (fuel 2) and Mirror copies (fuel 3). -/
theorem loeb_Dimcid_vs_Mirror_of_nec {d : ℕ} (hE : BoundedInnerNec d) :
    ∃ k₀ : ℕ, ∀ k : ℕ, k₀ < k →
      EvalGraph 2 (Dimcid k) Mirror (Dimcid k) 1 ∧ EvalGraph 3 Mirror (Dimcid k) Mirror 1 := by
  obtain ⟨k₀, h⟩ := loeb_Dimcid_vs_Mirror_core_of_nec hE
  exact ⟨k₀, fun k hk ↦ ⟨(h k hk).1.1, mirror_copies2_V (V := ℕ) (Dimcid k) 1 (h k hk).1.1⟩⟩


/-- **DIMCID × Mirror `(D, D)` in PA-`S'`, unconditional**: for all large `k`, `Dimcid k` defects
against Mirror and Mirror copies. -/
theorem loeb_Dimcid_vs_Mirror :
    ∃ k₀ : ℕ, ∀ k : ℕ, k₀ < k →
      EvalGraph 2 (Dimcid k) Mirror (Dimcid k) 1 ∧ EvalGraph 3 Mirror (Dimcid k) Mirror 1 :=
  loeb_Dimcid_vs_Mirror_of_nec boundedInnerNec_sixteen


end mirrorCell

/-! ### 9. Cell 3 — DIMCID × Cupod `(D, D)`, the MUTUAL family -/

section cupodCell

/-! #### Cupod's description, and the two searchers' search clauses against any opponent -/


/-! #### The hand-written template `guardTemplate a`, filled with two arbitrary description triples -/


/-! #### Cupod's guard against DIMCID, its transposition, and the mutual family -/


/-! #### The slack of a two-level ∧-elimination: `(14, 16)` -/

/-- Two ∧-eliminations (`8·(x+y)+7` then `8·(u+v)+7`, with `x = u + v + 1`) are below the family slack
`(14, 16)` at `z = x + y + 1` (for VARIABLE lengths, so that `push_cast` never sees a quote). -/
lemma slack4_le (a x y u v z : V) (hx : x = u + v + 1) (hz : z = x + y + 1) :
    a + 8 * (x + y) + 7 + 8 * (u + v) + 7 ≤ a + ((14 : ℕ) : V) + ((16 : ℕ) : V) * z := by
  have h := slack_depth_le a z [(x, y), (u, v)] (by
    intro p hp
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hp
    rcases hp with rfl | rfl
    · subst hz; exact le_self_add
    · subst hx hz; exact le_trans le_self_add (le_trans le_self_add le_self_add))
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, List.length_cons, List.length_nil,
    add_zero] at h
  push_cast at h ⊢
  exact le_trans (le_of_eq (by ring)) (le_trans h (le_of_eq (by ring)))

/-- The same with the inner conjunction on the RIGHT (`y = u + v + 1`). -/
lemma slack4_le' (a x y u v z : V) (hy : y = u + v + 1) (hz : z = x + y + 1) :
    a + 8 * (x + y) + 7 + 8 * (u + v) + 7 ≤ a + ((14 : ℕ) : V) + ((16 : ℕ) : V) * z := by
  have h := slack_depth_le a z [(x, y), (u, v)] (by
    intro p hp
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hp
    rcases hp with rfl | rfl
    · subst hz; exact le_self_add
    · subst hy hz; exact le_trans le_self_add (le_trans le_add_self le_self_add))
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, List.length_cons, List.length_nil,
    add_zero] at h
  push_cast at h ⊢
  exact le_trans (le_of_eq (by ring)) (le_trans h (le_of_eq (by ring)))

/-- The same at `ℕ`, in the `le_def` shape. -/
lemma slack4_nat (a x y u v z k : ℕ) (hx : x = u + v + 1) (hz : z = x + y + 1) (h : a + 14 + 16 * z ≤ k) :
    a + 8 * (x + y) + 7 + 8 * (u + v) + 7 = k ∨ a + 8 * (x + y) + 7 + 8 * (u + v) + 7 < k := by
  have h1 := le_def.mp (slack4_le (V := ℕ) a x y u v z hx hz)
  simp only [natCast_nat] at h1
  exact le_def_trans h1 (Nat.eq_or_lt_of_le h)

lemma slack4_nat' (a x y u v z k : ℕ) (hy : y = u + v + 1) (hz : z = x + y + 1) (h : a + 14 + 16 * z ≤ k) :
    a + 8 * (x + y) + 7 + 8 * (u + v) + 7 = k ∨ a + 8 * (x + y) + 7 + 8 * (u + v) + 7 < k := by
  have h1 := le_def.mp (slack4_le' (V := ℕ) a x y u v z hy hz)
  simp only [natCast_nat] at h1
  exact le_def_trans h1 (Nat.eq_or_lt_of_le h)


/-! #### `pDC` in both readings -/


/-! #### The Löb premise and the cells -/


end cupodCell

end ArithS
