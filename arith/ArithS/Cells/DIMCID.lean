import ArithS.Cells.DupocMirror
import ArithS.Necessitation.Package
import PrisonersDilemma.Bots.LlmGenerations.DIMCID

/-!
# ArithS.Cells.DIMCID — DIMCID × DIMCID, DIMCID × Mirror and DIMCID × Cupod, all `(D, D)`, in PA-`S'`

`Research/Notes/ROUTE_B_SCOPE.md` §3 Phase 2 (2026-09-23): the DIMCID family — the arithmetized
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

1. **The guard is the GENERAL translation `tmpl`** (`Code.lean`), not the hand-written `GtmplA`:
   `tmplD := tmpl phiD` with `phiD := .impl (.plays .self .opp C) (.plays .opp .self D)`, a closed
   constant never evaluated; `DimcidV k := pSearch k ⌜tmplD⌝ (pConst 1) (pConst 0)` and
   `pcode (PD.Bots.DIMCID k) = Dimcid k` (`pcode_DIMCID`, the bridge to the engine). Its
   transposition is the searcher on `tmplDT := tmpl phiD.transpose` with the branches swapped
   (`swapcode_DimcidV`, via `lMap_swap_tmpl` on the fragment) — τ(DIMCID) is not a zoo bot, and
   need not be: the swap reading of every fixed formula is handled by the transposed code exactly
   as `eval_qDM_swap_iff_V`. The canonical description (`innerDi`/`innerDT` irreducible, `gDi pDi
   qDi`, `uDi wDi`, the tower `TDi`, `dnum_DimcidV`/`dU_DimcidV`/`dW_DimcidV`, `val_TDi_V`,
   `relabel_val_uDi_wDi_V`, `relabel_val_uDiT_wDiT_V`) is `Instance`/`InstanceV` §2, `Transparency`
   §1 and `Prep` §2 re-run on the new constants.
2. **The truth of `tmpl` at a PRONOUN atom, in every model** (§3, NEW): `Det.models_trAt_plays_V`
   handles the `.plays` clause only for PROPER programs (`closedDesc`); DIMCID's guard has the bare
   pronouns `.self`/`.opp` (`progAux_self`/`progAux_opp`, the `descF` shape on the frame variables).
   `eval_tmpl_plays_self_opp_V`/`eval_tmpl_plays_opp_self_V`: at the frame
   `b = (x₁, u₁, w₁, x₂, u₂, w₂)`, "`relabel u₁ w₁ x₁` plays `a` against `relabel u₂ w₂ x₂`" (and
   symmetrically) — by `Semiformula.eval_substs` on the ∃-prefix, `eval_relDesc_V`/`eval_evalG_V`
   (`Det.lean`, already V-generic) and the `Matrix.cons_val` simproc. Then `eval_tmplD_V`/
   `eval_tmplDT_V`: the template is the implication of the two atoms. Nothing in `Code.lean`/
   `Agent.lean`/`Det.lean`/`Instance*.lean` was changed.

The fixed formulas are stated GENERICALLY in the opponent's description triple `(X, U, W)` (`X` a
one-variable term in the budget, `U W` closed): `qDG X U W := tmplD ⇜ ![TDi, cl uDi, cl wDi, X,
cl U, cl W]` and the transposed `qTG`, with `lMap swap (qDG X U W) = qTG (swap X) (swap U) (swap W)`;
the truth equations (`eval_qDG_iff_V`, `eval_qTG_iff_V`) take the hypothesis "the triple describes
`opp` in `stdActV V`", the instance equations on codes (`guardCode_DimcidV_eq_instB`,
`guardCode_DimcidTV_eq_instB` — the latter via `relabelTemplate_gsubst`, as `Prep` §1) take the
three code-level description hypotheses, and the conjunction family `pG X U W := qDG X U W ⋏ qTG
(swap X) (swap U) (swap W)` (the `Prep` §3 / `DupocMirror` §5 move) gives `pG_both_V`/`pG_guards_V`
by ∧-elimination on codes and `eval_pG_iff_std/_swap` (the same content in both readings). A cell
is then the five hypotheses for its opponent plus `LoebSound _ 7 8`:
* **Cell 1 (§7)**: `(TDi, uDi, wDi)` describes `DimcidV k` itself; `qDD`, `pDD`, `loebSound_pDD`,
  `dimcid_self_cell_core`, **`dimcid_self_defect_unconditional`** (`EvalGraph 2 (Dimcid k)
  (Dimcid k) (Dimcid k) 1` for all large `k`), `dimcid_finds_guard_unconditional` (the box form),
  and the engine-facing `dimcid_finds_guardOf_unconditional` (`Agent.guardOf phiD (DIMCID k)
  (DIMCID k)` is `TAct`-provable within `k`).
* **Cell 2 (§8)**: `(cl TM, numT 0, numT 1)` describes `MirrorV` (`Cells/DupocMirror`, reused: `TM`,
  `MirrorV`, `mirror_step_V`); `qDMi`, `pDMi`, `loebSound_pDMi` (Mirror COPIES at fuel 3, the
  generic `mirror_copies_V`), **`dimcid_mirror_defect_unconditional`** (`Dimcid k` defects at fuel 2
  and Mirror defects back at fuel 3), `dimcid_finds_guard_vs_mirror_unconditional`.
* **Cell 3 (§9), the MUTUAL family** (the engine's `outcome_DIMCID_vs_CupodBot = (D, D)`,
  `mutual_pblt_engine_id`): `(TD, uC, wC)` describes `CupodV k` (`dU_CupodV`/`dW_CupodV`,
  `dnum_CupodV_eq`, new here) and its transposition describes `DupocV k`. DIMCID's guard against
  Cupod says "Cupod plays D against me", which Cupod only does if IT finds ITS guard ("DIMCID plays D
  against me") — so the family is the four-guard conjunction `pDC := pG TD uC wC ⋏ pCD`, `pCD := qCD
  ⋏ lMap swap qCD`, with `qCD := qG 1 TD uC wC TDi uDi wDi` Cupod's guard against DIMCID on the
  hand-written template (`qG a X U W X' U' W' := GtmplA a ⇜ ![X, cl U, cl W, X', cl U', cl W']`, the
  fully generic instance equation `guardCode_GtmplA_eq_instB` / `_swap_eq_instB` and truth equation
  `eval_qG_iff_V`, both taking description hypotheses — `InstanceV` §4 / `DupocMirror` §2–3 with both
  triples as parameters). A box of `pDC(k)` yields the four guard boxes by a TWO-level ∧-elimination
  (`pDC_all_V`, slack `(14, 16)`: `slack4_le`/`slack4_nat`), so all four searchers commit at fuel 2 —
  DIMCID defects against Cupod, Cupod defects against DIMCID, the transposed searcher cooperates with
  Dupoc, Dupoc cooperates with it — which makes every conjunct true in both readings
  (`loebSound_pDC : LoebSound pDC 14 16`); **`dimcid_cupod_defect_unconditional`** (both defect at
  fuel 2) and `dimcid_cupod_find_guards_unconditional` (both boxes).

Conventions (`HANDOVER_ARITHMETIZED_S.md` §5–6): every threshold and constant is EXISTENTIAL; `simp`
never sees a closed quote of `tmplD`/`qDD`/`pDD` (the quote equations are for VARIABLE sentences,
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

lemma phiD_transpose : phiD.transpose = .impl (.plays .self .opp .D) (.plays .opp .self .C) := rfl

lemma fragF_phiD : fragF phiD = true := rfl

/-- The six-variable template of DIMCID's guard (a CLOSED constant, never evaluated). -/
noncomputable def tmplD : Semisentence LAct 6 := tmpl phiD

/-- The template of the transposed guard. -/
noncomputable def tmplDT : Semisentence LAct 6 := tmpl phiD.transpose

lemma tmplD_eq : tmplD = tmpl (.plays .self .opp .C) 🡒 tmpl (.plays .opp .self .D) := tmpl_impl _ _

lemma tmplDT_eq : tmplDT = tmpl (.plays .self .opp .D) 🡒 tmpl (.plays .opp .self .C) := tmpl_impl _ _

lemma lMap_swap_tmplD : Semiformula.lMap swap tmplD = tmplDT := lMap_swap_tmpl phiD fragF_phiD

lemma lMap_swap_tmplDT : Semiformula.lMap swap tmplDT = tmplD := by
  rw [← lMap_swap_tmplD, lMap_swap_swap]


end template

/-! ### 1. DIMCID in every model, and its transposition -/

section dimcid

/-- `DIMCID k` in an arbitrary model: search the guard within budget `k`; found ⇒ `D` (`pConst 1`),
else `C` (`pConst 0`). -/
noncomputable def DimcidV (k : V) : V := pSearch k (⌜tmplD⌝ : V) (pConst 1) (pConst 0)

/-- The transposed searcher (τ(DIMCID)): its guard is the transposed template, found ⇒ `C`. -/
noncomputable def DimcidTV (k : V) : V := pSearch k (⌜tmplDT⌝ : V) (pConst 0) (pConst 1)

/-- `DimcidV` IS the generic engine searcher `SV tmplD 1` of `Cells/Common/Bots` (up to the casts of the
branch constants) — the bridge the consolidation map asks for; `DupocV` has NO such bridge. -/
lemma DimcidV_eq_SV (k : V) : DimcidV k = SV tmplD 1 k := by
  unfold DimcidV SV; norm_num

lemma DimcidTV_eq_SV (k : V) : DimcidTV k = SV tmplDT 0 k := by
  unfold DimcidTV SV; norm_num

/-- `DIMCID k` at `ℕ`. -/
noncomputable def Dimcid (k : ℕ) : ℕ := DimcidV (V := ℕ) k

lemma DimcidV_nat (k : ℕ) : DimcidV (V := ℕ) k = Dimcid k := rfl

/-- **The bridge to the engine**: the code of the engine's `DIMCID k` is `Dimcid k`. -/
theorem pcode_DIMCID (k : ℕ) : pcode (PD.Bots.DIMCID k) = Dimcid k := by
  simp [PD.Bots.DIMCID, actCode]; rfl

theorem swapcode_DimcidV (k : V) : swapcode (DimcidV k) = DimcidTV k := by
  unfold DimcidV DimcidTV swapcode
  rw [relabel_search, relabel_const, relabel_const, relabelTemplate_quote_sentence₆_V, lMap_swap_tmplD]
  simp [relabelAct]

theorem swapcode_DimcidTV (k : V) : swapcode (DimcidTV k) = DimcidV k := by
  rw [← swapcode_DimcidV, swapcode_swapcode]

end dimcid

/-! ### 2. The canonical description of `DimcidV k` is `k`-independent apart from the budget -/

section canonical

/-- The budget-independent inner part of DIMCID's code. -/
noncomputable def innerDi : ℕ := ppair (⌜tmplD⌝ : ℕ) (ppair (pConst 1) (pConst 0))

/-- The budget-independent inner part of the transposed searcher's code. -/
noncomputable def innerDT : ℕ := ppair (⌜tmplDT⌝ : ℕ) (ppair (pConst 0) (pConst 1))

lemma innerDi_def : innerDi = ppair (⌜tmplD⌝ : ℕ) (ppair (pConst 1) (pConst 0)) := rfl
lemma innerDT_def : innerDT = ppair (⌜tmplDT⌝ : ℕ) (ppair (pConst 0) (pConst 1)) := rfl

/- Closed constants built from the giant templates: never to be evaluated. -/
attribute [irreducible] innerDi innerDT

lemma cast_innerDi : ((innerDi : ℕ) : V) = ppair (⌜tmplD⌝ : V) (ppair (pConst 1) (pConst 0)) := by
  rw [innerDi_def, cast_ppair, cast_ppair, cast_pConst, cast_pConst, coe_quote_sentence₆]
  push_cast
  rfl

lemma cast_innerDT : ((innerDT : ℕ) : V) = ppair (⌜tmplDT⌝ : V) (ppair (pConst 0) (pConst 1)) := by
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

/-- The stored template of the canonical searcher (`⌜tmplD⌝` or `⌜tmplDT⌝`). -/
noncomputable def gDi : ℕ := if innerDi ≤ innerDT then (⌜tmplD⌝ : ℕ) else (⌜tmplDT⌝ : ℕ)
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
    DimcidV k = pSearch k ((⌜tmplD⌝ : ℕ) : V) ((pConst 1 : ℕ) : V) ((pConst 0 : ℕ) : V) := by
  unfold DimcidV; rw [coe_quote_sentence₆, cast_pConst, cast_pConst]; push_cast; rfl

lemma DimcidTV_eq_cast (k : V) :
    DimcidTV k = pSearch k ((⌜tmplDT⌝ : ℕ) : V) ((pConst 0 : ℕ) : V) ((pConst 1 : ℕ) : V) := by
  unfold DimcidTV; rw [coe_quote_sentence₆, cast_pConst, cast_pConst]; push_cast; rfl

/-- **The canonical code of `DimcidV k` is a searcher with the (cast) `k`-independent inner triple.** -/
theorem dnum_DimcidV (k : V) : dnum (DimcidV k) = pSearch k (gDi : V) (pDi : V) (qDi : V) := by
  by_cases h : innerDi ≤ innerDT
  · simp only [gDi, pDi, qDi, if_pos h]
    rcases Nat.lt_or_eq_of_le h with h' | h'
    · rw [dnum_of_lt (by rw [swapcode_DimcidV]; exact (DimcidV_lt_DimcidTV_iff k).mpr h')]
      exact DimcidV_eq_cast k
    · rw [dnum_of_eq (by rw [swapcode_DimcidV, DimcidV_eq_inner, DimcidTV_eq_inner, h'])]
      exact DimcidV_eq_cast k
  · simp only [gDi, pDi, qDi, if_neg h]
    rw [dnum_of_gt (by rw [swapcode_DimcidV]; exact (DimcidTV_lt_DimcidV_iff k).mpr (Nat.lt_of_not_le h)),
      swapcode_DimcidV]
    exact DimcidTV_eq_cast k

theorem dU_DimcidV (k : V) : dU (DimcidV k) = (⌜uDi⌝ : V) := by
  unfold dU uDi
  rw [swapcode_DimcidV]
  by_cases h1 : innerDi < innerDT
  · rw [if_pos ((DimcidV_lt_DimcidTV_iff k).mpr h1), if_pos h1, quote_cterm_C]
  · rw [if_neg (fun h ↦ h1 ((DimcidV_lt_DimcidTV_iff k).mp h)), if_neg h1]
    by_cases h2 : innerDT < innerDi
    · rw [if_pos ((DimcidTV_lt_DimcidV_iff k).mpr h2), if_pos h2, quote_cterm_D]
    · rw [if_neg (fun h ↦ h2 ((DimcidTV_lt_DimcidV_iff k).mp h)), if_neg h2, quote_numT]
      simp

theorem dW_DimcidV (k : V) : dW (DimcidV k) = (⌜wDi⌝ : V) := by
  unfold dW wDi
  rw [swapcode_DimcidV]
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
    ppairT (bnum 6) (ppairT (^#0) (ppairT (bnum (gDi : V)) (ppairT (progT (pDi : V)) (progT (qDi : V))))) ^+ 𝟏 := by
  unfold TDi
  rw [term_emb_lMap_emb_n, quote_term_lMap_emb, quote_emb_searchT1]

/-- **`TDi` at the budget `k` denotes the canonical code of `DimcidV k`** (in `stdActV V`). -/
theorem val_TDi_V (k : V) : TDi.val (s := stdActV V) ![k] Empty.elim = dnum (DimcidV k) := by
  unfold TDi
  rw [Semiterm.val_lMap, stdActV_lMap_emb, val_searchT1_V, dnum_DimcidV]

/-- The `k`-independent re-valuation terms reconstruct `DimcidV k` from its canonical code. -/
theorem relabel_val_uDi_wDi_V (k : V) :
    relabel (uDi.val (s := stdActV V) ![] Empty.elim) (wDi.val (s := stdActV V) ![] Empty.elim)
      (dnum (DimcidV k)) = DimcidV k := by
  unfold uDi wDi
  by_cases h1 : innerDi < innerDT
  · rw [if_pos h1, if_pos h1, val_cterm_C_V, val_cterm_D_V,
      dnum_of_lt (by rw [swapcode_DimcidV]; exact (DimcidV_lt_DimcidTV_iff k).mpr h1), relabel_zero_one]
  · rw [if_neg h1, if_neg h1]
    by_cases h2 : innerDT < innerDi
    · rw [if_pos h2, if_pos h2, val_cterm_D_V, val_cterm_C_V,
        dnum_of_gt (by rw [swapcode_DimcidV]; exact (DimcidTV_lt_DimcidV_iff k).mpr h2)]
      exact swapcode_swapcode _
    · have h' : innerDi = innerDT := le_antisymm (not_lt.mp h2) (not_lt.mp h1)
      rw [if_neg h2, if_neg h2, val_numT_V, val_numT_V, Nat.cast_zero, Nat.cast_one,
        dnum_of_eq (by rw [swapcode_DimcidV, DimcidV_eq_inner, DimcidTV_eq_inner, h']), relabel_zero_one]

/-- The transposed re-valuation terms. -/
noncomputable def uDiT : ClosedSemiterm LAct 0 := Semiterm.lMap swap uDi
noncomputable def wDiT : ClosedSemiterm LAct 0 := Semiterm.lMap swap wDi

/-- The transposed descriptions reconstruct `DimcidTV k` from the canonical code of `DimcidV k`. -/
theorem relabel_val_uDiT_wDiT_V (k : V) :
    relabel (uDiT.val (s := stdActV V) ![] Empty.elim) (wDiT.val (s := stdActV V) ![] Empty.elim)
      (dnum (DimcidV k)) = DimcidTV k := by
  unfold uDiT wDiT uDi wDi
  by_cases h1 : innerDi < innerDT
  · rw [if_pos h1, if_pos h1, lMap_swap_cterm_C, lMap_swap_cterm_D, val_cterm_D_V, val_cterm_C_V,
      dnum_of_lt (by rw [swapcode_DimcidV]; exact (DimcidV_lt_DimcidTV_iff k).mpr h1)]
    exact swapcode_DimcidV k
  · rw [if_neg h1, if_neg h1]
    by_cases h2 : innerDT < innerDi
    · rw [if_pos h2, if_pos h2, lMap_swap_cterm_D, lMap_swap_cterm_C, val_cterm_C_V, val_cterm_D_V,
        dnum_of_gt (by rw [swapcode_DimcidV]; exact (DimcidTV_lt_DimcidV_iff k).mpr h2), swapcode_DimcidV,
        relabel_zero_one]
    · have h' : innerDi = innerDT := le_antisymm (not_lt.mp h2) (not_lt.mp h1)
      have hDT : DimcidV k = DimcidTV k := by rw [DimcidV_eq_inner, DimcidTV_eq_inner, h']
      rw [if_neg h2, if_neg h2, lMap_swap_numT, lMap_swap_numT, val_numT_V, val_numT_V, Nat.cast_zero,
        Nat.cast_one, dnum_of_eq (by rw [swapcode_DimcidV, hDT]), relabel_zero_one, hDT]

end canonical

/-! ### 3. The pronoun atoms of `tmpl` in every model, and the truth of the guard template -/

section atoms

/-- **The `.plays .self .opp a` atom of `tmpl` in every model**: at the frame
`b = (x₁, u₁, w₁, x₂, u₂, w₂)`, "me (`relabel u₁ w₁ x₁`) plays `a` against opp
(`relabel u₂ w₂ x₂`)". -/
lemma eval_tmpl_plays_self_opp_V (a : PD.Action) (b : Fin 6 → V) :
    Semiformula.Eval (s := stdActV V) b Empty.elim (tmpl (.plays .self .opp a)) ↔
      ∃ n, EvalGraph n (relabel (b 1) (b 2) (b 0)) (relabel (b 4) (b 5) (b 3))
        (relabel (b 1) (b 2) (b 0)) (actCode a : V) := by
  rw [tmpl_plays]
  unfold progGraph
  rw [progAux_self, progAux_opp]
  unfold descF
  simp only [Semiformula.eval_substs, Semiformula.eval_ex, LogicalConnective.HomClass.map_and,
    LogicalConnective.Prop.and_eq, Semiformula.eval_rel, eval_relDesc_V, eval_evalG_V, stdActV_rel_eq,
    Function.comp_def, Matrix.cons_val, Semiterm.val_bvar, val_cl_V, val_actT_V]
  constructor
  · rintro ⟨x, y, N, ⟨d, rfl, rfl⟩, ⟨d', rfl, rfl⟩, h⟩
    exact ⟨N, h⟩
  · rintro ⟨N, h⟩
    exact ⟨_, _, N, ⟨_, rfl, rfl⟩, ⟨_, rfl, rfl⟩, h⟩

/-- **The `.plays .opp .self a` atom of `tmpl` in every model**: "opp plays `a` against me". -/
lemma eval_tmpl_plays_opp_self_V (a : PD.Action) (b : Fin 6 → V) :
    Semiformula.Eval (s := stdActV V) b Empty.elim (tmpl (.plays .opp .self a)) ↔
      ∃ n, EvalGraph n (relabel (b 4) (b 5) (b 3)) (relabel (b 1) (b 2) (b 0))
        (relabel (b 4) (b 5) (b 3)) (actCode a : V) := by
  rw [tmpl_plays]
  unfold progGraph
  rw [progAux_self, progAux_opp]
  unfold descF
  simp only [Semiformula.eval_substs, Semiformula.eval_ex, LogicalConnective.HomClass.map_and,
    LogicalConnective.Prop.and_eq, Semiformula.eval_rel, eval_relDesc_V, eval_evalG_V, stdActV_rel_eq,
    Function.comp_def, Matrix.cons_val, Semiterm.val_bvar, val_cl_V, val_actT_V]
  constructor
  · rintro ⟨x, y, N, ⟨d, rfl, rfl⟩, ⟨d', rfl, rfl⟩, h⟩
    exact ⟨N, h⟩
  · rintro ⟨N, h⟩
    exact ⟨_, _, N, ⟨_, rfl, rfl⟩, ⟨_, rfl, rfl⟩, h⟩

/-- **The truth of DIMCID's guard template at a frame**: "me plays C against opp" implies "opp
plays D against me". -/
theorem eval_tmplD_V (b : Fin 6 → V) :
    Semiformula.Eval (s := stdActV V) b Empty.elim tmplD ↔
      ((∃ n, EvalGraph n (relabel (b 1) (b 2) (b 0)) (relabel (b 4) (b 5) (b 3)) (relabel (b 1) (b 2) (b 0)) 0) →
        (∃ n, EvalGraph n (relabel (b 4) (b 5) (b 3)) (relabel (b 1) (b 2) (b 0)) (relabel (b 4) (b 5) (b 3)) 1)) := by
  rw [tmplD_eq]
  simp only [LogicalConnective.HomClass.map_imply, LogicalConnective.Prop.arrow_eq,
    eval_tmpl_plays_self_opp_V, eval_tmpl_plays_opp_self_V, actCode, Nat.cast_zero, Nat.cast_one]

/-- **The truth of the transposed guard template at a frame**: "me plays D against opp" implies
"opp plays C against me". -/
theorem eval_tmplDT_V (b : Fin 6 → V) :
    Semiformula.Eval (s := stdActV V) b Empty.elim tmplDT ↔
      ((∃ n, EvalGraph n (relabel (b 1) (b 2) (b 0)) (relabel (b 4) (b 5) (b 3)) (relabel (b 1) (b 2) (b 0)) 1) →
        (∃ n, EvalGraph n (relabel (b 4) (b 5) (b 3)) (relabel (b 1) (b 2) (b 0)) (relabel (b 4) (b 5) (b 3)) 0)) := by
  rw [tmplDT_eq]
  simp only [LogicalConnective.HomClass.map_imply, LogicalConnective.Prop.arrow_eq,
    eval_tmpl_plays_self_opp_V, eval_tmpl_plays_opp_self_V, actCode, Nat.cast_zero, Nat.cast_one]

end atoms

/-! ### 4. The fixed formulas, generic in the opponent's description triple -/

section fixedFormulas

/-- **The fixed formula of DIMCID against an opponent described by `(X, U, W)`** (`X` a one-variable
term in the budget, `U W` closed): `tmplD` filled with DIMCID's description in the me-slots. -/
noncomputable def qDG (X : Semiterm LAct Empty 1) (U W : ClosedSemiterm LAct 0) : Semisentence LAct 1 :=
  tmplD ⇜ ![TDi, cl uDi, cl wDi, X, cl U, cl W]

/-- **The fixed formula of the transposed searcher** against `(X, U, W)`. -/
noncomputable def qTG (X : Semiterm LAct Empty 1) (U W : ClosedSemiterm LAct 0) : Semisentence LAct 1 :=
  tmplDT ⇜ ![TDi, cl uDiT, cl wDiT, X, cl U, cl W]

lemma lMap_swap_qDG (X : Semiterm LAct Empty 1) (U W : ClosedSemiterm LAct 0) :
    Semiformula.lMap swap (qDG X U W) =
      qTG (Semiterm.lMap swap X) (Semiterm.lMap swap U) (Semiterm.lMap swap W) := by
  unfold qDG qTG
  rw [Semiformula.lMap_subst, lMap_swap_tmplD]
  congr 1
  funext i
  fin_cases i <;> simp [lMap_swap_TDi, lMap_swap_cl, uDiT, wDiT]

lemma lMap_swap_qTG (X : Semiterm LAct Empty 1) (U W : ClosedSemiterm LAct 0) :
    Semiformula.lMap swap (qTG X U W) =
      qDG (Semiterm.lMap swap X) (Semiterm.lMap swap U) (Semiterm.lMap swap W) := by
  unfold qDG qTG
  rw [Semiformula.lMap_subst, lMap_swap_tmplDT]
  congr 1
  funext i
  fin_cases i <;> simp [lMap_swap_TDi, lMap_swap_cl, uDiT, wDiT, term_lMap_swap_swap]

/-- **The truth equation of `qDG X U W` in every model** (standard reading), given that the triple
describes `opp` at the budget `k`: "`DimcidV k` plays C against `opp`" implies "`opp` plays D
against `DimcidV k`". -/
theorem eval_qDG_iff_V (k : V) (X : Semiterm LAct Empty 1) (U W : ClosedSemiterm LAct 0) {opp : V}
    (hopp : relabel (U.val (s := stdActV V) ![] Empty.elim) (W.val (s := stdActV V) ![] Empty.elim)
      (X.val (s := stdActV V) ![k] Empty.elim) = opp) :
    Semiformula.Eval (s := stdActV V) ![k] Empty.elim (qDG X U W) ↔
      ((∃ n, EvalGraph n (DimcidV k) opp (DimcidV k) 0) → (∃ n, EvalGraph n opp (DimcidV k) opp 1)) := by
  unfold qDG
  rw [Semiformula.eval_substs]
  have h0 : (Semiterm.val (s := stdActV V) ![k] Empty.elim ∘ ![TDi, cl uDi, cl wDi, X, cl U, cl W]) =
      ![dnum (DimcidV k), uDi.val (s := stdActV V) ![] Empty.elim, wDi.val (s := stdActV V) ![] Empty.elim,
        X.val (s := stdActV V) ![k] Empty.elim, U.val (s := stdActV V) ![] Empty.elim,
        W.val (s := stdActV V) ![] Empty.elim] := by
    funext i; fin_cases i <;> simp [val_TDi_V, val_cl_V]
  rw [h0, eval_tmplD_V]
  simp only [Matrix.cons_val]
  rw [relabel_val_uDi_wDi_V, hopp]

/-- **The truth equation of `qTG X U W` in every model** (standard reading): "`DimcidTV k` plays D
against `opp`" implies "`opp` plays C against `DimcidTV k`". -/
theorem eval_qTG_iff_V (k : V) (X : Semiterm LAct Empty 1) (U W : ClosedSemiterm LAct 0) {opp : V}
    (hopp : relabel (U.val (s := stdActV V) ![] Empty.elim) (W.val (s := stdActV V) ![] Empty.elim)
      (X.val (s := stdActV V) ![k] Empty.elim) = opp) :
    Semiformula.Eval (s := stdActV V) ![k] Empty.elim (qTG X U W) ↔
      ((∃ n, EvalGraph n (DimcidTV k) opp (DimcidTV k) 1) → (∃ n, EvalGraph n opp (DimcidTV k) opp 0)) := by
  unfold qTG
  rw [Semiformula.eval_substs]
  have h0 : (Semiterm.val (s := stdActV V) ![k] Empty.elim ∘ ![TDi, cl uDiT, cl wDiT, X, cl U, cl W]) =
      ![dnum (DimcidV k), uDiT.val (s := stdActV V) ![] Empty.elim, wDiT.val (s := stdActV V) ![] Empty.elim,
        X.val (s := stdActV V) ![k] Empty.elim, U.val (s := stdActV V) ![] Empty.elim,
        W.val (s := stdActV V) ![] Empty.elim] := by
    funext i; fin_cases i <;> simp [val_TDi_V, val_cl_V]
  rw [h0, eval_tmplDT_V]
  simp only [Matrix.cons_val]
  rw [relabel_val_uDiT_wDiT_V, hopp]

omit [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁] in
/-- The swapped reading of `qDG` is the standard reading of the transposed `qTG`. -/
theorem eval_qDG_swap_iff_V (k : V) (X : Semiterm LAct Empty 1) (U W : ClosedSemiterm LAct 0) :
    Semiformula.Eval (s := swapActS V) ![k] Empty.elim (qDG X U W) ↔
      Semiformula.Eval (s := stdActV V) ![k] Empty.elim
        (qTG (Semiterm.lMap swap X) (Semiterm.lMap swap U) (Semiterm.lMap swap W)) := by
  rw [eval_swapActS, lMap_swap_qDG, ← stdActV_eq_stdActS]

omit [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁] in
theorem eval_qTG_swap_iff_V (k : V) (X : Semiterm LAct Empty 1) (U W : ClosedSemiterm LAct 0) :
    Semiformula.Eval (s := swapActS V) ![k] Empty.elim (qTG X U W) ↔
      Semiformula.Eval (s := stdActV V) ![k] Empty.elim
        (qDG (Semiterm.lMap swap X) (Semiterm.lMap swap U) (Semiterm.lMap swap W)) := by
  rw [eval_swapActS, lMap_swap_qTG, ← stdActV_eq_stdActS]

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

lemma semitermVec_val_qDG (X : Semiterm LAct Empty 1) (U W : ClosedSemiterm LAct 0) :
    SemitermVec.val (fun i ↦ (⌜(Rew.emb ((![TDi, cl uDi, cl wDi, X, cl U, cl W] :
      Fin 6 → Semiterm LAct Empty 1) i) : SyntacticSemiterm LAct 1)⌝ : Bootstrapping.Semiterm V LAct 1)) =
      qDGVec X U W := by
  have hv : (fun i ↦ (⌜(Rew.emb ((![TDi, cl uDi, cl wDi, X, cl U, cl W] :
      Fin 6 → Semiterm LAct Empty 1) i) : SyntacticSemiterm LAct 1)⌝ : Bootstrapping.Semiterm V LAct 1)) =
      ![⌜(Rew.emb TDi : SyntacticSemiterm LAct 1)⌝,
        ⌜(Rew.emb (cl uDi : Semiterm LAct Empty 1) : SyntacticSemiterm LAct 1)⌝,
        ⌜(Rew.emb (cl wDi : Semiterm LAct Empty 1) : SyntacticSemiterm LAct 1)⌝,
        ⌜(Rew.emb X : SyntacticSemiterm LAct 1)⌝,
        ⌜(Rew.emb (cl U : Semiterm LAct Empty 1) : SyntacticSemiterm LAct 1)⌝,
        ⌜(Rew.emb (cl W : Semiterm LAct Empty 1) : SyntacticSemiterm LAct 1)⌝] := by
    funext i; fin_cases i <;> rfl
  rw [hv]
  simp only [SemitermVec.val_cons, SemitermVec.val_nil]
  rfl

/-- The code of `qDG X U W` is the internal substitution of `qDGVec X U W` into the template code. -/
theorem quote_qDG (X : Semiterm LAct Empty 1) (U W : ClosedSemiterm LAct 0) :
    (⌜qDG X U W⌝ : V) = subst LAct (qDGVec X U W) (⌜tmplD⌝ : V) := by
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

/-- Substituting `bnum k` into the six codes gives the description vector of `(DimcidV k, opp)`,
given that the opponent's triple describes `opp` on codes. -/
theorem termSubstVec_qDGVec (k : V) (X : Semiterm LAct Empty 1) (U W : ClosedSemiterm LAct 0) {opp : V}
    (hX : termSubst LAct (bnum k ∷ (0 : V)) (⌜(Rew.emb X : SyntacticSemiterm LAct 1)⌝ : V) = progT (dnum opp))
    (hU : (⌜U⌝ : V) = dU opp) (hW : (⌜W⌝ : V) = dW opp) :
    termSubstVec LAct 6 (bnum k ∷ (0 : V)) (qDGVec X U W) = descVec (DimcidV k) opp := by
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
  have sT : termSubst LAct (bnum k ∷ 0) (⌜(Rew.emb TDi : SyntacticSemiterm LAct 1)⌝ : V) =
      progT (dnum (DimcidV k)) := by
    rw [quote_emb_TDi, termSubst_tower, dnum_DimcidV]
  have sU : termSubst LAct (bnum k ∷ 0) (⌜(Rew.emb (cl uDi : Semiterm LAct Empty 1) : SyntacticSemiterm LAct 1)⌝ : V) =
      dU (DimcidV k) := by
    rw [quote_emb_cl_V, termSubst_closed _ (semiterm_quote_emb₀ _), dU_DimcidV, Semiterm.empty_quote_def]
  have sW : termSubst LAct (bnum k ∷ 0) (⌜(Rew.emb (cl wDi : Semiterm LAct Empty 1) : SyntacticSemiterm LAct 1)⌝ : V) =
      dW (DimcidV k) := by
    rw [quote_emb_cl_V, termSubst_closed _ (semiterm_quote_emb₀ _), dW_DimcidV, Semiterm.empty_quote_def]
  have sU2 : termSubst LAct (bnum k ∷ 0) (⌜(Rew.emb (cl U : Semiterm LAct Empty 1) : SyntacticSemiterm LAct 1)⌝ : V) =
      dU opp := by
    rw [quote_emb_cl_V, termSubst_closed _ (semiterm_quote_emb₀ _), ← Semiterm.empty_quote_def, hU]
  have sW2 : termSubst LAct (bnum k ∷ 0) (⌜(Rew.emb (cl W : Semiterm LAct Empty 1) : SyntacticSemiterm LAct 1)⌝ : V) =
      dW opp := by
    rw [quote_emb_cl_V, termSubst_closed _ (semiterm_quote_emb₀ _), ← Semiterm.empty_quote_def, hW]
  unfold qDGVec descVec
  rw [six_eq, termSubstVec_cons hT e5, termSubstVec_cons hU' e4, termSubstVec_cons hW' e3,
    termSubstVec_cons hX' e2, termSubstVec_cons hU'' e1, termSubstVec_cons hW'' e0, termSubstVec_nil,
    sT, sU, sW, hX, sU2, sW2]

/-- **DIMCID's instance equation on codes, in every model**: the guard code of `DimcidV k` against
`opp` is the `bnum k`-instance of `⌜qDG X U W⌝` whenever `(X, U, W)` describes `opp` on codes. -/
theorem guardCode_DimcidV_eq_instB (k : V) (X : Semiterm LAct Empty 1) (U W : ClosedSemiterm LAct 0) {opp : V}
    (hX : termSubst LAct (bnum k ∷ (0 : V)) (⌜(Rew.emb X : SyntacticSemiterm LAct 1)⌝ : V) = progT (dnum opp))
    (hU : (⌜U⌝ : V) = dU opp) (hW : (⌜W⌝ : V) = dW opp) :
    guardCode (⌜tmplD⌝ : V) (DimcidV k) opp = instB (⌜qDG X U W⌝ : V) k := by
  show guardCode (⌜tmplD⌝ : V) (DimcidV k) opp = subst LAct (bnum k ∷ (0 : V)) (⌜qDG X U W⌝ : V)
  rw [quote_qDG, substs_substs (p := (⌜tmplD⌝ : V)) (l := 6)
    (by simpa using Sentence.quote_isSemiformula (V := V) tmplD)
    (bnum_cons_semitermVec k) (qDGVec_semitermVec X U W), termSubstVec_qDGVec k X U W hX hU hW]
  rfl

/-- The transposed searcher's guard code against `swapcode opp` is the code-level τ of DIMCID's
against `opp`. -/
lemma guardCode_DimcidTV_eq_relabel (k opp : V) :
    guardCode (⌜tmplDT⌝ : V) (DimcidTV k) (swapcode opp) =
      relabelTemplate 1 0 (guardCode (⌜tmplD⌝ : V) (DimcidV k) opp) := by
  have hg0 : IsSemiformula LAct 6 (⌜tmplD⌝ : V) := by
    simpa using Sentence.quote_isSemiformula (V := V) tmplD
  have hg1 : IsSemiformula LAct 6 (⌜tmplDT⌝ : V) := by
    simpa using Sentence.quote_isSemiformula (V := V) tmplDT
  rw [← gsubst_of_template hg0, relabelTemplate_gsubst, swapcode_DimcidV, relabelTemplate_quote_sentence₆_V,
    lMap_swap_tmplD, gsubst_of_template hg1]

/-- **The transposed searcher's instance equation on codes, in every model.** -/
theorem guardCode_DimcidTV_eq_instB (k : V) (X : Semiterm LAct Empty 1) (U W : ClosedSemiterm LAct 0) {opp : V}
    (hX : termSubst LAct (bnum k ∷ (0 : V)) (⌜(Rew.emb X : SyntacticSemiterm LAct 1)⌝ : V) = progT (dnum opp))
    (hU : (⌜U⌝ : V) = dU opp) (hW : (⌜W⌝ : V) = dW opp) :
    guardCode (⌜tmplDT⌝ : V) (DimcidTV k) (swapcode opp) =
      instB (⌜qTG (Semiterm.lMap swap X) (Semiterm.lMap swap U) (Semiterm.lMap swap W)⌝ : V) k := by
  rw [guardCode_DimcidTV_eq_relabel, guardCode_DimcidV_eq_instB k X U W hX hU hW]
  unfold instB
  rw [relabelTemplate_subst isAct_one isAct_zero (Sentence.quote_isSemiformul₁ (qDG X U W))
    (bnum_cons_semitermVec k), relabelTemplate_quote_sentence_V, lMap_swap_qDG]
  congr 1
  rw [show (1 : V) = 0 + 1 by simp, termRelabelVec_cons (bnum_term_LAct k).isUTerm IsUTermVec.empty,
    termRelabelVec_nil, termRelabel_bnum]

/-! #### The search clauses -/

/-- **DIMCID's search clause in every model** (fuel `2`): a proof of its guard within the budget
makes `DimcidV k` DEFECT (`pConst 1`). -/
theorem dimcid_search_V (k opp : V) :
    LenProvableV TAct k (guardCode (⌜tmplD⌝ : V) (DimcidV k) opp) →
      EvalGraph 2 (DimcidV k) opp (DimcidV k) 1 := by
  intro h
  rw [show (2 : V) = 1 + 1 from one_add_one_eq_two.symm]
  show EvalGraph (1 + 1) (DimcidV k) opp (pSearch k (⌜tmplD⌝ : V) (pConst 1) (pConst 0)) 1
  rw [EvalGraph.search_iff₆ (isSemiformula_quote₆ tmplD)]
  left
  refine ⟨h, ?_⟩
  have e : EvalGraph (0 + 1) (DimcidV k) opp (pConst 1) 1 := EvalGraph.const_iff.mpr rfl
  rwa [zero_add] at e

/-- **The transposed searcher's search clause in every model** (fuel `2`): found ⇒ `C`. -/
theorem dimcidT_search_V (k opp : V) :
    LenProvableV TAct k (guardCode (⌜tmplDT⌝ : V) (DimcidTV k) opp) →
      EvalGraph 2 (DimcidTV k) opp (DimcidTV k) 0 := by
  intro h
  rw [show (2 : V) = 1 + 1 from one_add_one_eq_two.symm]
  show EvalGraph (1 + 1) (DimcidTV k) opp (pSearch k (⌜tmplDT⌝ : V) (pConst 0) (pConst 1)) 0
  rw [EvalGraph.search_iff₆ (isSemiformula_quote₆ tmplDT)]
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
`≤ a` makes `DimcidV k` defect against `opp` and `DimcidTV k` cooperate with `swapcode opp`
(fuel 2), given the code-level description hypotheses. -/
theorem pG_both_V (k : V) (X : Semiterm LAct Empty 1) (U W : ClosedSemiterm LAct 0) {opp : V}
    (hX : termSubst LAct (bnum k ∷ (0 : V)) (⌜(Rew.emb X : SyntacticSemiterm LAct 1)⌝ : V) = progT (dnum opp))
    (hU : (⌜U⌝ : V) = dU opp) (hW : (⌜W⌝ : V) = dW opp) : ∀ a : V,
    a + 8 * (formulaLen LAct (instB (⌜qDG X U W⌝ : V) k) +
      formulaLen LAct (instB (⌜qTG (Semiterm.lMap swap X) (Semiterm.lMap swap U) (Semiterm.lMap swap W)⌝ : V) k))
      + 7 ≤ k →
    LenDerivable TAct a (instB (⌜pG X U W⌝ : V) k) →
    EvalGraph 2 (DimcidV k) opp (DimcidV k) 1 ∧ EvalGraph 2 (DimcidTV k) (swapcode opp) (DimcidTV k) 0 := by
  intro a ha h
  rw [instB_quote_pG] at h
  have hx := isFormula_instB_quote (qDG X U W) k
  have hy := isFormula_instB_quote (qTG (Semiterm.lMap swap X) (Semiterm.lMap swap U) (Semiterm.lMap swap W)) k
  have h₁ := lenDerivable_mono_V ha (lenDerivable_andL_V hx hy h)
  have h₂ := lenDerivable_mono_V ha (lenDerivable_andR_V hx hy h)
  rw [lenDerivable_iff_lenProvableV, ← guardCode_DimcidV_eq_instB k X U W hX hU hW] at h₁
  rw [lenDerivable_iff_lenProvableV, ← guardCode_DimcidTV_eq_instB k X U W hX hU hW] at h₂
  exact ⟨dimcid_search_V k opp h₁, dimcidT_search_V k _ h₂⟩

/-- **Both searchers FIND their guards** (the box form of `pG_both_V`). -/
theorem pG_guards_V (k : V) (X : Semiterm LAct Empty 1) (U W : ClosedSemiterm LAct 0) {opp : V}
    (hX : termSubst LAct (bnum k ∷ (0 : V)) (⌜(Rew.emb X : SyntacticSemiterm LAct 1)⌝ : V) = progT (dnum opp))
    (hU : (⌜U⌝ : V) = dU opp) (hW : (⌜W⌝ : V) = dW opp) (a : V)
    (ha : a + 8 * (formulaLen LAct (instB (⌜qDG X U W⌝ : V) k) +
      formulaLen LAct (instB (⌜qTG (Semiterm.lMap swap X) (Semiterm.lMap swap U) (Semiterm.lMap swap W)⌝ : V) k))
      + 7 ≤ k)
    (hpc : LenDerivable TAct a (instB (⌜pG X U W⌝ : V) k)) :
    LenProvableV TAct k (guardCode (⌜tmplD⌝ : V) (DimcidV k) opp) ∧
    LenProvableV TAct k (guardCode (⌜tmplDT⌝ : V) (DimcidTV k) (swapcode opp)) := by
  rw [instB_quote_pG] at hpc
  have hx := isFormula_instB_quote (qDG X U W) k
  have hy := isFormula_instB_quote (qTG (Semiterm.lMap swap X) (Semiterm.lMap swap U) (Semiterm.lMap swap W)) k
  have h₁ := lenDerivable_mono_V ha (lenDerivable_andL_V hx hy hpc)
  have h₂ := lenDerivable_mono_V ha (lenDerivable_andR_V hx hy hpc)
  rw [lenDerivable_iff_lenProvableV, ← guardCode_DimcidV_eq_instB k X U W hX hU hW] at h₁
  rw [lenDerivable_iff_lenProvableV, ← guardCode_DimcidTV_eq_instB k X U W hX hU hW] at h₂
  exact ⟨h₁, h₂⟩

/-! #### `pG` in both readings -/

/-- `pG(k)` in the standard reading, given that the triple describes `opp` and the transposed
triple describes `opp'` (in every intended instance, `opp' = swapcode opp`). -/
theorem eval_pG_iff_std (k : V) (X : Semiterm LAct Empty 1) (U W : ClosedSemiterm LAct 0) {opp opp' : V}
    (hopp : relabel (U.val (s := stdActV V) ![] Empty.elim) (W.val (s := stdActV V) ![] Empty.elim)
      (X.val (s := stdActV V) ![k] Empty.elim) = opp)
    (hopp' : relabel ((Semiterm.lMap swap U).val (s := stdActV V) ![] Empty.elim)
      ((Semiterm.lMap swap W).val (s := stdActV V) ![] Empty.elim)
      ((Semiterm.lMap swap X).val (s := stdActV V) ![k] Empty.elim) = opp') :
    Semiformula.Eval (s := stdActV V) ![k] Empty.elim (pG X U W) ↔
      ((∃ n, EvalGraph n (DimcidV k) opp (DimcidV k) 0) → (∃ n, EvalGraph n opp (DimcidV k) opp 1)) ∧
      ((∃ n, EvalGraph n (DimcidTV k) opp' (DimcidTV k) 1) → (∃ n, EvalGraph n opp' (DimcidTV k) opp' 0)) := by
  rw [pG_def]
  simp only [LogicalConnective.HomClass.map_and, LogicalConnective.Prop.and_eq]
  rw [eval_qDG_iff_V k X U W hopp, eval_qTG_iff_V k _ _ _ hopp']

/-- `pG(k)` in the swapped reading: the SAME content (the conjuncts exchange roles). -/
theorem eval_pG_iff_swap (k : V) (X : Semiterm LAct Empty 1) (U W : ClosedSemiterm LAct 0) {opp opp' : V}
    (hopp : relabel (U.val (s := stdActV V) ![] Empty.elim) (W.val (s := stdActV V) ![] Empty.elim)
      (X.val (s := stdActV V) ![k] Empty.elim) = opp)
    (hopp' : relabel ((Semiterm.lMap swap U).val (s := stdActV V) ![] Empty.elim)
      ((Semiterm.lMap swap W).val (s := stdActV V) ![] Empty.elim)
      ((Semiterm.lMap swap X).val (s := stdActV V) ![k] Empty.elim) = opp') :
    Semiformula.Eval (s := swapActS V) ![k] Empty.elim (pG X U W) ↔
      ((∃ n, EvalGraph n (DimcidV k) opp (DimcidV k) 0) → (∃ n, EvalGraph n opp (DimcidV k) opp 1)) ∧
      ((∃ n, EvalGraph n (DimcidTV k) opp' (DimcidTV k) 1) → (∃ n, EvalGraph n opp' (DimcidTV k) opp' 0)) := by
  rw [eval_swapActS, lMap_swap_pG, ← stdActV_eq_stdActS]
  simp only [LogicalConnective.HomClass.map_and, LogicalConnective.Prop.and_eq]
  rw [eval_qDG_iff_V k X U W hopp, eval_qTG_iff_V k _ _ _ hopp', and_comm]

/-- `pG(k)` in the standard reading, `stdActS` form. -/
theorem eval_pG_iff_stdActS (k : V) (X : Semiterm LAct Empty 1) (U W : ClosedSemiterm LAct 0) {opp opp' : V}
    (hopp : relabel (U.val (s := stdActV V) ![] Empty.elim) (W.val (s := stdActV V) ![] Empty.elim)
      (X.val (s := stdActV V) ![k] Empty.elim) = opp)
    (hopp' : relabel ((Semiterm.lMap swap U).val (s := stdActV V) ![] Empty.elim)
      ((Semiterm.lMap swap W).val (s := stdActV V) ![] Empty.elim)
      ((Semiterm.lMap swap X).val (s := stdActV V) ![k] Empty.elim) = opp') :
    Semiformula.Eval (s := stdActS V) ![k] Empty.elim (pG X U W) ↔
      ((∃ n, EvalGraph n (DimcidV k) opp (DimcidV k) 0) → (∃ n, EvalGraph n opp (DimcidV k) opp 1)) ∧
      ((∃ n, EvalGraph n (DimcidTV k) opp' (DimcidTV k) 1) → (∃ n, EvalGraph n opp' (DimcidTV k) opp' 0)) := by
  rw [← stdActV_eq_stdActS]; exact eval_pG_iff_std k X U W hopp hopp'

end conj

/-! ### 7. Cell 1 — DIMCID × DIMCID `(D, D)` -/

section selfCell

/-- DIMCID's own triple describes `DimcidV k` on codes: the `X`-hypothesis. -/
lemma hX_self (k : V) :
    termSubst LAct (bnum k ∷ (0 : V)) (⌜(Rew.emb TDi : SyntacticSemiterm LAct 1)⌝ : V) =
      progT (dnum (DimcidV k)) := by
  rw [quote_emb_TDi, termSubst_tower, dnum_DimcidV]

lemma hU_self (k : V) : (⌜uDi⌝ : V) = dU (DimcidV k) := (dU_DimcidV k).symm
lemma hW_self (k : V) : (⌜wDi⌝ : V) = dW (DimcidV k) := (dW_DimcidV k).symm

/-- DIMCID's own triple describes `DimcidV k` in `stdActV V`. -/
lemma hopp_self (k : V) :
    relabel (uDi.val (s := stdActV V) ![] Empty.elim) (wDi.val (s := stdActV V) ![] Empty.elim)
      (TDi.val (s := stdActV V) ![k] Empty.elim) = DimcidV k := by
  rw [val_TDi_V]; exact relabel_val_uDi_wDi_V k

/-- The transposed triple describes `DimcidTV k` in `stdActV V`. -/
lemma hopp'_self (k : V) :
    relabel ((Semiterm.lMap swap uDi).val (s := stdActV V) ![] Empty.elim)
      ((Semiterm.lMap swap wDi).val (s := stdActV V) ![] Empty.elim)
      ((Semiterm.lMap swap TDi).val (s := stdActV V) ![k] Empty.elim) = DimcidTV k := by
  rw [lMap_swap_TDi, val_TDi_V]; exact relabel_val_uDiT_wDiT_V k

/-- **The fixed formula of DIMCID against itself**: `qDD(k)` says "`DimcidV k` plays C against
itself implies `DimcidV k` plays D against itself". -/
noncomputable def qDD : Semisentence LAct 1 := qDG TDi uDi wDi

lemma qDD_def : qDD = qDG TDi uDi wDi := rfl

/-- **The instance equation on codes**: DIMCID's guard code against itself is the `bnum k`-instance
of `⌜qDD⌝`, in every model. -/
theorem guardCode_DimcidV_self_eq_instB (k : V) :
    guardCode (⌜tmplD⌝ : V) (DimcidV k) (DimcidV k) = instB (⌜qDD⌝ : V) k :=
  guardCode_DimcidV_eq_instB k TDi uDi wDi (hX_self k) (hU_self k) (hW_self k)

/-- **The truth equation of `qDD` in every model** (standard reading). -/
theorem eval_qDD_iff_V (k : V) :
    Semiformula.Eval (s := stdActV V) ![k] Empty.elim qDD ↔
      ((∃ n, EvalGraph n (DimcidV k) (DimcidV k) (DimcidV k) 0) →
        (∃ n, EvalGraph n (DimcidV k) (DimcidV k) (DimcidV k) 1)) :=
  eval_qDG_iff_V k TDi uDi wDi (hopp_self k)

/-- **The truth equation of `qDD` in the swapped reading**: the transposed searcher against itself,
"D implies C". -/
theorem eval_qDD_swap_iff_V (k : V) :
    Semiformula.Eval (s := swapActS V) ![k] Empty.elim qDD ↔
      ((∃ n, EvalGraph n (DimcidTV k) (DimcidTV k) (DimcidTV k) 1) →
        (∃ n, EvalGraph n (DimcidTV k) (DimcidTV k) (DimcidTV k) 0)) := by
  rw [qDD_def, eval_qDG_swap_iff_V]
  exact eval_qTG_iff_V k _ _ _ (hopp'_self k)

/-- **The Löb family of the self-play cell**: `pDD := qDD ⋏ (its transposition)`. -/
noncomputable def pDD : Semisentence LAct 1 := pG TDi uDi wDi

lemma pDD_def : pDD = pG TDi uDi wDi := rfl

/-- **The bounded Löb premise of the self-play family, slack `(7, 8)`**: a proof code of `pDD(k)` of
length `a` with `a + 7 + 8·|pDD(k)| ≤ k` makes both searchers find their guards, so `DimcidV k`
defects and `DimcidTV k` cooperates (fuel 2), which makes both implications TRUE (their
consequents hold) in both readings. -/
theorem loebSound_pDD : LoebSound pDD 7 8 := by
  intro V _ _ k a ha h
  have : V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁ := inferInstance
  have ha' : a + 8 * (formulaLen LAct (instB (⌜qDG TDi uDi wDi⌝ : V) k) +
      formulaLen LAct (instB (⌜qTG (Semiterm.lMap swap TDi) (Semiterm.lMap swap uDi) (Semiterm.lMap swap wDi)⌝ : V) k))
      + 7 ≤ k :=
    le_trans (pConj_slack_le a _ _ _ (formulaLen_instB_pG TDi uDi wDi k)) ha
  obtain ⟨h1, h2⟩ := pG_both_V k TDi uDi wDi (hX_self k) (hU_self k) (hW_self k) a ha' h
  rw [swapcode_DimcidV] at h2
  exact ⟨(eval_pG_iff_stdActS k TDi uDi wDi (hopp_self k) (hopp'_self k)).mpr ⟨fun _ ↦ ⟨2, h1⟩, fun _ ↦ ⟨2, h2⟩⟩,
    (eval_pG_iff_swap k TDi uDi wDi (hopp_self k) (hopp'_self k)).mpr ⟨fun _ ↦ ⟨2, h1⟩, fun _ ↦ ⟨2, h2⟩⟩⟩

/-- **The self-play cell, packaged**: for all large `k`, both searchers find their guards against
themselves (fuel 2) and both guard boxes hold — `family_found pDD` (the arithmetized `pblt_engine`)
then ∧-elimination on codes. -/
theorem dimcid_self_cell_core {d : ℕ} (hE : BoundedInnerNec d) :
    ∃ k₀ : ℕ, ∀ k : ℕ, k₀ < k →
      (EvalGraph 2 (Dimcid k) (Dimcid k) (Dimcid k) 1 ∧
        EvalGraph 2 (DimcidTV (V := ℕ) k) (DimcidTV k) (DimcidTV k) 0) ∧
      (LenProvableV TAct k (guardCode (⌜tmplD⌝ : ℕ) (Dimcid k) (Dimcid k)) ∧
        LenProvableV TAct k (guardCode (⌜tmplDT⌝ : ℕ) (DimcidTV (V := ℕ) k) (DimcidTV k))) := by
  obtain ⟨k₀, h⟩ := family_found pDD hE loebSound_pDD
  refine ⟨k₀, fun k hk ↦ ?_⟩
  obtain ⟨a, ha, hpc⟩ := h k hk
  have ha' := le_def.mpr (pConj_slack_nat a _ _ _ k (formulaLen_instB_pG (V := ℕ) TDi uDi wDi k) ha)
  have h1 := pG_both_V (V := ℕ) k TDi uDi wDi (hX_self k) (hU_self k) (hW_self k) a ha' hpc
  have h2 := pG_guards_V (V := ℕ) k TDi uDi wDi (hX_self k) (hU_self k) (hW_self k) a ha' hpc
  rw [swapcode_DimcidV] at h1 h2
  exact ⟨h1, h2⟩

/-- **DIMCID × DIMCID is `(D, D)` in PA-`S'`, conditional on bounded inner necessitation**: for all
large `k`, `Dimcid k` defects against itself (fuel 2). -/
theorem dimcid_self_defect {d : ℕ} (hE : BoundedInnerNec d) :
    ∃ k₀ : ℕ, ∀ k : ℕ, k₀ < k → EvalGraph 2 (Dimcid k) (Dimcid k) (Dimcid k) 1 := by
  obtain ⟨k₀, h⟩ := dimcid_self_cell_core hE
  exact ⟨k₀, fun k hk ↦ (h k hk).1.1⟩

/-- **The box form**: for all large `k`, DIMCID actually FINDS a proof of its guard against itself
within its budget `k` (conditional). -/
theorem dimcid_finds_guard {d : ℕ} (hE : BoundedInnerNec d) :
    ∃ k₀ : ℕ, ∀ k : ℕ, k₀ < k → LenProvableV TAct k (guardCode (⌜tmplD⌝ : ℕ) (Dimcid k) (Dimcid k)) := by
  obtain ⟨k₀, h⟩ := dimcid_self_cell_core hE
  exact ⟨k₀, fun k hk ↦ (h k hk).2.1⟩

/-- **DIMCID × DIMCID `(D, D)` in PA-`S'`, unconditional**: for all large `k`, `Dimcid k` defects
against itself. -/
theorem dimcid_self_defect_unconditional :
    ∃ k₀ : ℕ, ∀ k : ℕ, k₀ < k → EvalGraph 2 (Dimcid k) (Dimcid k) (Dimcid k) 1 :=
  dimcid_self_defect boundedInnerNec_sixteen

/-- **DIMCID finds its guard against itself, unconditional.** -/
theorem dimcid_finds_guard_unconditional :
    ∃ k₀ : ℕ, ∀ k : ℕ, k₀ < k → LenProvableV TAct k (guardCode (⌜tmplD⌝ : ℕ) (Dimcid k) (Dimcid k)) :=
  dimcid_finds_guard boundedInnerNec_sixteen

/-- The consulted guard of the engine's `DIMCID k` against itself (`Agent.guardOf`) is the guard
code of `Dimcid k` on `tmplD`. -/
lemma guardOf_DIMCID (k : ℕ) :
    guardOf phiD (PD.Bots.DIMCID k) (PD.Bots.DIMCID k) = guardCode (⌜tmplD⌝ : ℕ) (Dimcid k) (Dimcid k) := by
  unfold guardOf; rw [pcode_DIMCID]; rfl

/-- **The engine-facing form, unconditional**: for all large `k`, the guard the arithmetized evaluator
consults for the engine's `DIMCID k` against itself has a `TAct`-proof within the budget `k`. -/
theorem dimcid_finds_guardOf_unconditional :
    ∃ k₀ : ℕ, ∀ k : ℕ, k₀ < k → LenProvableV TAct k (guardOf phiD (PD.Bots.DIMCID k) (PD.Bots.DIMCID k)) := by
  obtain ⟨k₀, h⟩ := dimcid_finds_guard_unconditional
  exact ⟨k₀, fun k hk ↦ by rw [guardOf_DIMCID]; exact h k hk⟩

end selfCell

/-! ### 8. Cell 2 — DIMCID × Mirror `(D, D)` -/

section mirrorCell

/-- Mirror copies, in every model: a fuel-2 play of `opp` against Mirror is Mirror's fuel-3 play
against `opp` (`mirror_step_V`). -/
theorem mirror_copies_V (opp a : V) (h : EvalGraph 2 opp MirrorV opp a) :
    EvalGraph 3 MirrorV opp MirrorV a := by
  rw [show (3 : V) = 2 + 1 from two_add_one_eq_three.symm]
  exact (mirror_step_V 2 opp a).mpr h

/-- Mirror's closed triple describes `MirrorV` on codes: the `X`-hypothesis. -/
lemma hX_mirror (k : V) :
    termSubst LAct (bnum k ∷ (0 : V))
      (⌜(Rew.emb (cl TM : Semiterm LAct Empty 1) : SyntacticSemiterm LAct 1)⌝ : V) = progT (dnum MirrorV) := by
  rw [quote_emb_cl_V, termSubst_closed _ (semiterm_quote_emb₀ _), quote_emb_TM, dnum_MirrorV]

lemma hU_mirror : (⌜numT 0⌝ : V) = dU MirrorV := by
  rw [Semiterm.empty_quote_def, quote_emb_numT, dU_MirrorV, Nat.cast_zero]

lemma hW_mirror : (⌜numT 1⌝ : V) = dW MirrorV := by
  rw [Semiterm.empty_quote_def, quote_emb_numT, dW_MirrorV, Nat.cast_one]

/-- Mirror's closed triple describes `MirrorV` in `stdActV V`. -/
lemma hopp_mirror (k : V) :
    relabel ((numT 0).val (s := stdActV V) ![] Empty.elim) ((numT 1).val (s := stdActV V) ![] Empty.elim)
      ((cl TM : Semiterm LAct Empty 1).val (s := stdActV V) ![k] Empty.elim) = MirrorV := by
  rw [val_numT_V, val_numT_V, Nat.cast_zero, Nat.cast_one, val_cl_V, val_TM_V, relabel_zero_one]

/-- The transposed triple still describes `MirrorV` (Mirror is τ-fixed). -/
lemma hopp'_mirror (k : V) :
    relabel ((Semiterm.lMap swap (numT 0)).val (s := stdActV V) ![] Empty.elim)
      ((Semiterm.lMap swap (numT 1)).val (s := stdActV V) ![] Empty.elim)
      ((Semiterm.lMap swap (cl TM : Semiterm LAct Empty 1)).val (s := stdActV V) ![k] Empty.elim) = MirrorV := by
  rw [lMap_swap_numT, lMap_swap_numT, lMap_swap_cl, lMap_swap_TM]
  exact hopp_mirror k

/-- **The fixed formula of DIMCID against Mirror**: `qDMi(k)` says "`DimcidV k` plays C against
Mirror implies Mirror plays D against `DimcidV k`". -/
noncomputable def qDMi : Semisentence LAct 1 := qDG (cl TM) (numT 0) (numT 1)

lemma qDMi_def : qDMi = qDG (cl TM) (numT 0) (numT 1) := rfl

/-- **The instance equation on codes**: DIMCID's guard code against Mirror is the `bnum k`-instance
of `⌜qDMi⌝`, in every model. -/
theorem guardCode_DimcidV_MirrorV_eq_instB (k : V) :
    guardCode (⌜tmplD⌝ : V) (DimcidV k) MirrorV = instB (⌜qDMi⌝ : V) k :=
  guardCode_DimcidV_eq_instB k (cl TM) (numT 0) (numT 1) (hX_mirror k) hU_mirror hW_mirror

/-- **The truth equation of `qDMi` in every model** (standard reading). -/
theorem eval_qDMi_iff_V (k : V) :
    Semiformula.Eval (s := stdActV V) ![k] Empty.elim qDMi ↔
      ((∃ n, EvalGraph n (DimcidV k) MirrorV (DimcidV k) 0) → (∃ n, EvalGraph n MirrorV (DimcidV k) MirrorV 1)) :=
  eval_qDG_iff_V k (cl TM) (numT 0) (numT 1) (hopp_mirror k)

/-- **The truth equation of `qDMi` in the swapped reading**: the transposed searcher against Mirror,
"D implies Mirror plays C". -/
theorem eval_qDMi_swap_iff_V (k : V) :
    Semiformula.Eval (s := swapActS V) ![k] Empty.elim qDMi ↔
      ((∃ n, EvalGraph n (DimcidTV k) MirrorV (DimcidTV k) 1) → (∃ n, EvalGraph n MirrorV (DimcidTV k) MirrorV 0)) := by
  rw [qDMi_def, eval_qDG_swap_iff_V]
  exact eval_qTG_iff_V k _ _ _ (hopp'_mirror k)

/-- **The Löb family of the Mirror cell**: `pDMi := qDMi ⋏ (its transposition)`. -/
noncomputable def pDMi : Semisentence LAct 1 := pG (cl TM) (numT 0) (numT 1)

lemma pDMi_def : pDMi = pG (cl TM) (numT 0) (numT 1) := rfl

/-- **The bounded Löb premise of the Mirror family, slack `(7, 8)`**: a box of `pDMi(k)` makes both
searchers find their guards against Mirror, `DimcidV k` defects and `DimcidTV k` cooperates
(fuel 2), Mirror COPIES (fuel 3), so both implications are true in both readings. -/
theorem loebSound_pDMi : LoebSound pDMi 7 8 := by
  intro V _ _ k a ha h
  have : V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁ := inferInstance
  have ha' : a + 8 * (formulaLen LAct (instB (⌜qDG (cl TM) (numT 0) (numT 1)⌝ : V) k) +
      formulaLen LAct (instB (⌜qTG (Semiterm.lMap swap (cl TM : Semiterm LAct Empty 1))
        (Semiterm.lMap swap (numT 0)) (Semiterm.lMap swap (numT 1))⌝ : V) k)) + 7 ≤ k :=
    le_trans (pConj_slack_le a _ _ _ (formulaLen_instB_pG (cl TM) (numT 0) (numT 1) k)) ha
  obtain ⟨h1, h2⟩ := pG_both_V k (cl TM) (numT 0) (numT 1) (hX_mirror k) hU_mirror hW_mirror a ha' h
  rw [swapcode_MirrorV] at h2
  exact ⟨(eval_pG_iff_stdActS k (cl TM) (numT 0) (numT 1) (hopp_mirror k) (hopp'_mirror k)).mpr
      ⟨fun _ ↦ ⟨3, mirror_copies_V _ _ h1⟩, fun _ ↦ ⟨3, mirror_copies_V _ _ h2⟩⟩,
    (eval_pG_iff_swap k (cl TM) (numT 0) (numT 1) (hopp_mirror k) (hopp'_mirror k)).mpr
      ⟨fun _ ↦ ⟨3, mirror_copies_V _ _ h1⟩, fun _ ↦ ⟨3, mirror_copies_V _ _ h2⟩⟩⟩

/-- **The Mirror cell, packaged**: for all large `k`, both searchers find their guards against
Mirror (fuel 2) and both guard boxes hold. -/
theorem dimcid_mirror_cell_core {d : ℕ} (hE : BoundedInnerNec d) :
    ∃ k₀ : ℕ, ∀ k : ℕ, k₀ < k →
      (EvalGraph 2 (Dimcid k) Mirror (Dimcid k) 1 ∧ EvalGraph 2 (DimcidTV (V := ℕ) k) Mirror (DimcidTV k) 0) ∧
      (LenProvableV TAct k (guardCode (⌜tmplD⌝ : ℕ) (Dimcid k) Mirror) ∧
        LenProvableV TAct k (guardCode (⌜tmplDT⌝ : ℕ) (DimcidTV (V := ℕ) k) Mirror)) := by
  obtain ⟨k₀, h⟩ := family_found pDMi hE loebSound_pDMi
  refine ⟨k₀, fun k hk ↦ ?_⟩
  obtain ⟨a, ha, hpc⟩ := h k hk
  have ha' := le_def.mpr (pConj_slack_nat a _ _ _ k (formulaLen_instB_pG (V := ℕ) (cl TM) (numT 0) (numT 1) k) ha)
  have h1 := pG_both_V (V := ℕ) k (cl TM) (numT 0) (numT 1) (hX_mirror k) hU_mirror hW_mirror a ha' hpc
  have h2 := pG_guards_V (V := ℕ) k (cl TM) (numT 0) (numT 1) (hX_mirror k) hU_mirror hW_mirror a ha' hpc
  rw [swapcode_MirrorV] at h1 h2
  exact ⟨h1, h2⟩

/-- **DIMCID × Mirror is `(D, D)` in PA-`S'`, conditional on bounded inner necessitation**: for all
large `k`, `Dimcid k` defects against Mirror (fuel 2) and Mirror copies (fuel 3). -/
theorem dimcid_mirror_defect {d : ℕ} (hE : BoundedInnerNec d) :
    ∃ k₀ : ℕ, ∀ k : ℕ, k₀ < k →
      EvalGraph 2 (Dimcid k) Mirror (Dimcid k) 1 ∧ EvalGraph 3 Mirror (Dimcid k) Mirror 1 := by
  obtain ⟨k₀, h⟩ := dimcid_mirror_cell_core hE
  exact ⟨k₀, fun k hk ↦ ⟨(h k hk).1.1, mirror_copies_V (V := ℕ) (Dimcid k) 1 (h k hk).1.1⟩⟩

/-- **The box form**: for all large `k`, DIMCID FINDS a proof of its guard against Mirror within its
budget `k` (conditional). -/
theorem dimcid_finds_guard_vs_mirror {d : ℕ} (hE : BoundedInnerNec d) :
    ∃ k₀ : ℕ, ∀ k : ℕ, k₀ < k → LenProvableV TAct k (guardCode (⌜tmplD⌝ : ℕ) (Dimcid k) Mirror) := by
  obtain ⟨k₀, h⟩ := dimcid_mirror_cell_core hE
  exact ⟨k₀, fun k hk ↦ (h k hk).2.1⟩

/-- **DIMCID × Mirror `(D, D)` in PA-`S'`, unconditional**: for all large `k`, `Dimcid k` defects
against Mirror and Mirror copies. -/
theorem dimcid_mirror_defect_unconditional :
    ∃ k₀ : ℕ, ∀ k : ℕ, k₀ < k →
      EvalGraph 2 (Dimcid k) Mirror (Dimcid k) 1 ∧ EvalGraph 3 Mirror (Dimcid k) Mirror 1 :=
  dimcid_mirror_defect boundedInnerNec_sixteen

/-- **DIMCID finds its guard against Mirror, unconditional.** -/
theorem dimcid_finds_guard_vs_mirror_unconditional :
    ∃ k₀ : ℕ, ∀ k : ℕ, k₀ < k → LenProvableV TAct k (guardCode (⌜tmplD⌝ : ℕ) (Dimcid k) Mirror) :=
  dimcid_finds_guard_vs_mirror boundedInnerNec_sixteen

end mirrorCell

/-! ### 9. Cell 3 — DIMCID × Cupod `(D, D)`, the MUTUAL family -/

section cupodCell

/-! #### Cupod's description, and the two searchers' search clauses against any opponent -/

theorem swapcode_CupodV (k : V) : swapcode (CupodV k) = DupocV k := by
  rw [← swapcode_DupocV, swapcode_swapcode]

theorem dnum_CupodV_eq (k : V) : dnum (CupodV k) = dnum (DupocV k) := by
  rw [← swapcode_DupocV, dnum_swapcode]

theorem dU_CupodV (k : V) : dU (CupodV k) = (⌜uC⌝ : V) := by
  unfold dU uC uD
  rw [swapcode_CupodV]
  by_cases h1 : innerD < innerC
  · rw [if_neg (fun h ↦ lt_asymm ((DupocV_lt_CupodV_iff k).mpr h1) h), if_pos ((DupocV_lt_CupodV_iff k).mpr h1),
      if_pos h1, lMap_swap_cterm_C, quote_cterm_D]
  · rw [if_neg h1]
    by_cases h2 : innerC < innerD
    · rw [if_pos ((CupodV_lt_DupocV_iff k).mpr h2), if_pos h2, lMap_swap_cterm_D, quote_cterm_C]
    · rw [if_neg (fun h ↦ h2 ((CupodV_lt_DupocV_iff k).mp h)), if_neg (fun h ↦ h1 ((DupocV_lt_CupodV_iff k).mp h)),
        if_neg h2, lMap_swap_numT, quote_numT]
      simp

theorem dW_CupodV (k : V) : dW (CupodV k) = (⌜wC⌝ : V) := by
  unfold dW wC wD
  rw [swapcode_CupodV]
  by_cases h1 : innerD < innerC
  · rw [if_neg (fun h ↦ lt_asymm ((DupocV_lt_CupodV_iff k).mpr h1) h), if_pos ((DupocV_lt_CupodV_iff k).mpr h1),
      if_pos h1, lMap_swap_cterm_D, quote_cterm_C]
  · rw [if_neg h1]
    by_cases h2 : innerC < innerD
    · rw [if_pos ((CupodV_lt_DupocV_iff k).mpr h2), if_pos h2, lMap_swap_cterm_C, quote_cterm_D]
    · rw [if_neg (fun h ↦ h2 ((CupodV_lt_DupocV_iff k).mp h)), if_neg (fun h ↦ h1 ((DupocV_lt_CupodV_iff k).mp h)),
        if_neg h2, lMap_swap_numT, quote_numT]
      simp

/-- Cupod's triple `(TD, uC, wC)` describes `CupodV k` on codes: the `X`-hypothesis. -/
lemma hX_cupod (k : V) :
    termSubst LAct (bnum k ∷ (0 : V)) (⌜(Rew.emb TD : SyntacticSemiterm LAct 1)⌝ : V) =
      progT (dnum (CupodV k)) := by
  rw [quote_emb_TD, termSubst_tower, dnum_CupodV_eq, dnum_DupocV]

lemma hU_cupod (k : V) : (⌜uC⌝ : V) = dU (CupodV k) := (dU_CupodV k).symm
lemma hW_cupod (k : V) : (⌜wC⌝ : V) = dW (CupodV k) := (dW_CupodV k).symm

/-- Cupod's triple describes `CupodV k` in `stdActV V`. -/
lemma hopp_cupod (k : V) :
    relabel (uC.val (s := stdActV V) ![] Empty.elim) (wC.val (s := stdActV V) ![] Empty.elim)
      (TD.val (s := stdActV V) ![k] Empty.elim) = CupodV k := by
  rw [val_TD_V]; exact relabel_val_uC_wC_V k

/-- The transposed triple describes `DupocV k` in `stdActV V`. -/
lemma hopp'_cupod (k : V) :
    relabel ((Semiterm.lMap swap uC).val (s := stdActV V) ![] Empty.elim)
      ((Semiterm.lMap swap wC).val (s := stdActV V) ![] Empty.elim)
      ((Semiterm.lMap swap TD).val (s := stdActV V) ![k] Empty.elim) = DupocV k := by
  unfold uC wC
  rw [term_lMap_swap_swap, term_lMap_swap_swap, lMap_swap_TD, val_TD_V]
  exact relabel_val_uD_wD_V k

/-- Dupoc's own triple describes `DupocV k` on codes (as `hX_self`). -/
lemma hX_dupoc (k : V) :
    termSubst LAct (bnum k ∷ (0 : V)) (⌜(Rew.emb TD : SyntacticSemiterm LAct 1)⌝ : V) =
      progT (dnum (DupocV k)) := by
  rw [quote_emb_TD, termSubst_tower, dnum_DupocV]

lemma hU_dupoc (k : V) : (⌜uD⌝ : V) = dU (DupocV k) := (dU_DupocV k).symm
lemma hW_dupoc (k : V) : (⌜wD⌝ : V) = dW (DupocV k) := (dW_DupocV k).symm

/-- **Cupod's search clause against ANY opponent in every model** (fuel `2`). -/
theorem cupod_search_any_V (k opp : V) :
    LenProvableV TAct k (guardCode (⌜GtmplA 1⌝ : V) (CupodV k) opp) →
      EvalGraph 2 (CupodV k) opp (CupodV k) 1 := by
  intro h
  rw [show (2 : V) = 1 + 1 from one_add_one_eq_two.symm]
  show EvalGraph (1 + 1) (CupodV k) opp (pSearch k (⌜GtmplA 1⌝ : V) (pConst 1) (pConst 0)) 1
  rw [EvalGraph.search_iff₆ (isSemiformula_quote₆ (GtmplA 1))]
  left
  refine ⟨h, ?_⟩
  have e : EvalGraph (0 + 1) (CupodV k) opp (pConst 1) 1 := EvalGraph.const_iff.mpr rfl
  rwa [zero_add] at e

/-- **Dupoc's search clause against ANY opponent in every model** (fuel `2`). -/
theorem dupoc_search_any_V (k opp : V) :
    LenProvableV TAct k (guardCode (⌜GtmplA 0⌝ : V) (DupocV k) opp) →
      EvalGraph 2 (DupocV k) opp (DupocV k) 0 := by
  intro h
  rw [show (2 : V) = 1 + 1 from one_add_one_eq_two.symm]
  show EvalGraph (1 + 1) (DupocV k) opp (pSearch k (⌜GtmplA 0⌝ : V) (pConst 0) (pConst 1)) 0
  rw [EvalGraph.search_iff₆ (isSemiformula_quote₆ (GtmplA 0))]
  left
  refine ⟨h, ?_⟩
  rw [show (1 : V) = 0 + 1 by simp, EvalGraph.const_iff]

/-! #### The hand-written template `GtmplA a`, filled with two arbitrary description triples -/

/-- The template instance `GtmplA a` filled with the triples `(X, U, W)` (me) and `(X', U', W')` (opp). -/
noncomputable def qG (a : ℕ) (X : Semiterm LAct Empty 1) (U W : ClosedSemiterm LAct 0)
    (X' : Semiterm LAct Empty 1) (U' W' : ClosedSemiterm LAct 0) : Semisentence LAct 1 :=
  GtmplA a ⇜ ![X, cl U, cl W, X', cl U', cl W']

lemma lMap_swap_qG (a : ℕ) (X : Semiterm LAct Empty 1) (U W : ClosedSemiterm LAct 0)
    (X' : Semiterm LAct Empty 1) (U' W' : ClosedSemiterm LAct 0) :
    Semiformula.lMap swap (qG a X U W X' U' W') =
      qG (swapAct a) (Semiterm.lMap swap X) (Semiterm.lMap swap U) (Semiterm.lMap swap W)
        (Semiterm.lMap swap X') (Semiterm.lMap swap U') (Semiterm.lMap swap W') := by
  unfold qG
  rw [Semiformula.lMap_subst, lMap_swap_GtmplA]
  congr 1
  funext i
  fin_cases i <;> simp [lMap_swap_cl]

/-- The six codes of the substituted terms of `qG`, as an internal vector. -/
noncomputable def gVec (X : Semiterm LAct Empty 1) (U W : ClosedSemiterm LAct 0)
    (X' : Semiterm LAct Empty 1) (U' W' : ClosedSemiterm LAct 0) : V :=
  (⌜(Rew.emb X : SyntacticSemiterm LAct 1)⌝ : V) ∷
    ⌜(Rew.emb (cl U : Semiterm LAct Empty 1) : SyntacticSemiterm LAct 1)⌝ ∷
    ⌜(Rew.emb (cl W : Semiterm LAct Empty 1) : SyntacticSemiterm LAct 1)⌝ ∷
    ⌜(Rew.emb X' : SyntacticSemiterm LAct 1)⌝ ∷
    ⌜(Rew.emb (cl U' : Semiterm LAct Empty 1) : SyntacticSemiterm LAct 1)⌝ ∷
    ⌜(Rew.emb (cl W' : Semiterm LAct Empty 1) : SyntacticSemiterm LAct 1)⌝ ∷ 0

lemma semitermVec_val_gVec (X : Semiterm LAct Empty 1) (U W : ClosedSemiterm LAct 0)
    (X' : Semiterm LAct Empty 1) (U' W' : ClosedSemiterm LAct 0) :
    SemitermVec.val (fun i ↦ (⌜(Rew.emb ((![X, cl U, cl W, X', cl U', cl W'] :
      Fin 6 → Semiterm LAct Empty 1) i) : SyntacticSemiterm LAct 1)⌝ : Bootstrapping.Semiterm V LAct 1)) =
      gVec X U W X' U' W' := by
  have hv : (fun i ↦ (⌜(Rew.emb ((![X, cl U, cl W, X', cl U', cl W'] :
      Fin 6 → Semiterm LAct Empty 1) i) : SyntacticSemiterm LAct 1)⌝ : Bootstrapping.Semiterm V LAct 1)) =
      ![⌜(Rew.emb X : SyntacticSemiterm LAct 1)⌝,
        ⌜(Rew.emb (cl U : Semiterm LAct Empty 1) : SyntacticSemiterm LAct 1)⌝,
        ⌜(Rew.emb (cl W : Semiterm LAct Empty 1) : SyntacticSemiterm LAct 1)⌝,
        ⌜(Rew.emb X' : SyntacticSemiterm LAct 1)⌝,
        ⌜(Rew.emb (cl U' : Semiterm LAct Empty 1) : SyntacticSemiterm LAct 1)⌝,
        ⌜(Rew.emb (cl W' : Semiterm LAct Empty 1) : SyntacticSemiterm LAct 1)⌝] := by
    funext i; fin_cases i <;> rfl
  rw [hv]
  simp only [SemitermVec.val_cons, SemitermVec.val_nil]
  rfl

theorem quote_qG (a : ℕ) (X : Semiterm LAct Empty 1) (U W : ClosedSemiterm LAct 0)
    (X' : Semiterm LAct Empty 1) (U' W' : ClosedSemiterm LAct 0) :
    (⌜qG a X U W X' U' W'⌝ : V) = subst LAct (gVec X U W X' U' W') (⌜GtmplA a⌝ : V) := by
  unfold qG
  rw [Sentence.quote_def, Semiformula.coe_subst_eq_subst_coe, Semiformula.quote_def,
    Semiformula.typed_quote_substs, Bootstrapping.Semiformula.val_substs, ← Semiformula.quote_def,
    ← Sentence.quote_def]
  congr 1

lemma gVec_semitermVec (X : Semiterm LAct Empty 1) (U W : ClosedSemiterm LAct 0)
    (X' : Semiterm LAct Empty 1) (U' W' : ClosedSemiterm LAct 0) :
    IsSemitermVec LAct 6 1 (gVec X U W X' U' W' : V) := by
  rw [six_eq, gVec]
  exact ((((((IsSemitermVec.nil 1).adjoin (semiterm_quote_emb₁ _)).adjoin (semiterm_quote_emb₁ _)).adjoin
    (semiterm_quote_emb₁ _)).adjoin (semiterm_quote_emb₁ _)).adjoin (semiterm_quote_emb₁ _)).adjoin
    (semiterm_quote_emb₁ _)

/-- Substituting `bnum k` into the six codes gives the description vector of `(me, opp)`, given that
the two triples describe `me` and `opp` on codes. -/
theorem termSubstVec_gVec (k : V) (X : Semiterm LAct Empty 1) (U W : ClosedSemiterm LAct 0)
    (X' : Semiterm LAct Empty 1) (U' W' : ClosedSemiterm LAct 0) {me opp : V}
    (hX : termSubst LAct (bnum k ∷ (0 : V)) (⌜(Rew.emb X : SyntacticSemiterm LAct 1)⌝ : V) = progT (dnum me))
    (hU : (⌜U⌝ : V) = dU me) (hW : (⌜W⌝ : V) = dW me)
    (hX' : termSubst LAct (bnum k ∷ (0 : V)) (⌜(Rew.emb X' : SyntacticSemiterm LAct 1)⌝ : V) = progT (dnum opp))
    (hU' : (⌜U'⌝ : V) = dU opp) (hW' : (⌜W'⌝ : V) = dW opp) :
    termSubstVec LAct 6 (bnum k ∷ (0 : V)) (gVec X U W X' U' W') = descVec me opp := by
  have h1 : IsUTerm LAct (⌜(Rew.emb X : SyntacticSemiterm LAct 1)⌝ : V) := (semiterm_quote_emb₁ _).isUTerm
  have h2 : IsUTerm LAct (⌜(Rew.emb (cl U : Semiterm LAct Empty 1) : SyntacticSemiterm LAct 1)⌝ : V) :=
    (semiterm_quote_emb₁ _).isUTerm
  have h3 : IsUTerm LAct (⌜(Rew.emb (cl W : Semiterm LAct Empty 1) : SyntacticSemiterm LAct 1)⌝ : V) :=
    (semiterm_quote_emb₁ _).isUTerm
  have h4 : IsUTerm LAct (⌜(Rew.emb X' : SyntacticSemiterm LAct 1)⌝ : V) := (semiterm_quote_emb₁ _).isUTerm
  have h5 : IsUTerm LAct (⌜(Rew.emb (cl U' : Semiterm LAct Empty 1) : SyntacticSemiterm LAct 1)⌝ : V) :=
    (semiterm_quote_emb₁ _).isUTerm
  have h6 : IsUTerm LAct (⌜(Rew.emb (cl W' : Semiterm LAct Empty 1) : SyntacticSemiterm LAct 1)⌝ : V) :=
    (semiterm_quote_emb₁ _).isUTerm
  have e0 : IsUTermVec LAct 0 (0 : V) := IsUTermVec.empty
  have e1 := e0.adjoin h6
  have e2 := e1.adjoin h5
  have e3 := e2.adjoin h4
  have e4 := e3.adjoin h3
  have e5 := e4.adjoin h2
  have sU : termSubst LAct (bnum k ∷ 0) (⌜(Rew.emb (cl U : Semiterm LAct Empty 1) : SyntacticSemiterm LAct 1)⌝ : V) =
      dU me := by
    rw [quote_emb_cl_V, termSubst_closed _ (semiterm_quote_emb₀ _), ← Semiterm.empty_quote_def, hU]
  have sW : termSubst LAct (bnum k ∷ 0) (⌜(Rew.emb (cl W : Semiterm LAct Empty 1) : SyntacticSemiterm LAct 1)⌝ : V) =
      dW me := by
    rw [quote_emb_cl_V, termSubst_closed _ (semiterm_quote_emb₀ _), ← Semiterm.empty_quote_def, hW]
  have sU' : termSubst LAct (bnum k ∷ 0) (⌜(Rew.emb (cl U' : Semiterm LAct Empty 1) : SyntacticSemiterm LAct 1)⌝ : V) =
      dU opp := by
    rw [quote_emb_cl_V, termSubst_closed _ (semiterm_quote_emb₀ _), ← Semiterm.empty_quote_def, hU']
  have sW' : termSubst LAct (bnum k ∷ 0) (⌜(Rew.emb (cl W' : Semiterm LAct Empty 1) : SyntacticSemiterm LAct 1)⌝ : V) =
      dW opp := by
    rw [quote_emb_cl_V, termSubst_closed _ (semiterm_quote_emb₀ _), ← Semiterm.empty_quote_def, hW']
  unfold gVec descVec
  rw [six_eq, termSubstVec_cons h1 e5, termSubstVec_cons h2 e4, termSubstVec_cons h3 e3,
    termSubstVec_cons h4 e2, termSubstVec_cons h5 e1, termSubstVec_cons h6 e0, termSubstVec_nil,
    hX, sU, sW, hX', sU', sW']

/-- **The instance equation on codes for the hand-written template, in every model**: the guard code
of `me` against `opp` on `GtmplA a` is the `bnum k`-instance of `⌜qG a …⌝` whenever the two triples
describe `me` and `opp` on codes. -/
theorem guardCode_GtmplA_eq_instB (a : ℕ) (k : V) (X : Semiterm LAct Empty 1) (U W : ClosedSemiterm LAct 0)
    (X' : Semiterm LAct Empty 1) (U' W' : ClosedSemiterm LAct 0) {me opp : V}
    (hX : termSubst LAct (bnum k ∷ (0 : V)) (⌜(Rew.emb X : SyntacticSemiterm LAct 1)⌝ : V) = progT (dnum me))
    (hU : (⌜U⌝ : V) = dU me) (hW : (⌜W⌝ : V) = dW me)
    (hX' : termSubst LAct (bnum k ∷ (0 : V)) (⌜(Rew.emb X' : SyntacticSemiterm LAct 1)⌝ : V) = progT (dnum opp))
    (hU' : (⌜U'⌝ : V) = dU opp) (hW' : (⌜W'⌝ : V) = dW opp) :
    guardCode (⌜GtmplA a⌝ : V) me opp = instB (⌜qG a X U W X' U' W'⌝ : V) k := by
  show guardCode (⌜GtmplA a⌝ : V) me opp = subst LAct (bnum k ∷ (0 : V)) (⌜qG a X U W X' U' W'⌝ : V)
  rw [quote_qG, substs_substs (p := (⌜GtmplA a⌝ : V)) (l := 6)
    (by simpa using Sentence.quote_isSemiformula (V := V) (GtmplA a))
    (bnum_cons_semitermVec k) (gVec_semitermVec X U W X' U' W'),
    termSubstVec_gVec k X U W X' U' W' hX hU hW hX' hU' hW']
  rfl

/-- The transposed instance equation: the guard code of `swapcode me` against `swapcode opp` on
`GtmplA (swapAct a)` is the `bnum k`-instance of `⌜lMap swap (qG a …)⌝`. -/
theorem guardCode_GtmplA_swap_eq_instB (a : ℕ) (k : V) (X : Semiterm LAct Empty 1) (U W : ClosedSemiterm LAct 0)
    (X' : Semiterm LAct Empty 1) (U' W' : ClosedSemiterm LAct 0) {me opp : V}
    (hX : termSubst LAct (bnum k ∷ (0 : V)) (⌜(Rew.emb X : SyntacticSemiterm LAct 1)⌝ : V) = progT (dnum me))
    (hU : (⌜U⌝ : V) = dU me) (hW : (⌜W⌝ : V) = dW me)
    (hX' : termSubst LAct (bnum k ∷ (0 : V)) (⌜(Rew.emb X' : SyntacticSemiterm LAct 1)⌝ : V) = progT (dnum opp))
    (hU' : (⌜U'⌝ : V) = dU opp) (hW' : (⌜W'⌝ : V) = dW opp) :
    guardCode (⌜GtmplA (swapAct a)⌝ : V) (swapcode me) (swapcode opp) =
      instB (⌜Semiformula.lMap swap (qG a X U W X' U' W')⌝ : V) k := by
  have hg0 : IsSemiformula LAct 6 (⌜GtmplA a⌝ : V) := by
    simpa using Sentence.quote_isSemiformula (V := V) (GtmplA a)
  have hg1 : IsSemiformula LAct 6 (⌜GtmplA (swapAct a)⌝ : V) := by
    simpa using Sentence.quote_isSemiformula (V := V) (GtmplA (swapAct a))
  rw [← gsubst_of_template hg1, ← relabelTemplate_quote_GtmplA_V, ← relabelTemplate_gsubst, gsubst_of_template hg0,
    guardCode_GtmplA_eq_instB a k X U W X' U' W' hX hU hW hX' hU' hW']
  unfold instB
  rw [relabelTemplate_subst isAct_one isAct_zero (Sentence.quote_isSemiformul₁ (qG a X U W X' U' W'))
    (bnum_cons_semitermVec k), relabelTemplate_quote_sentence_V]
  congr 1
  rw [show (1 : V) = 0 + 1 by simp, termRelabelVec_cons (bnum_term_LAct k).isUTerm IsUTermVec.empty,
    termRelabelVec_nil, termRelabel_bnum]

/-- **The truth equation of `qG a …` in every model** (standard reading), given that the triples
describe `me` and `opp`: "`opp` plays `a` against `me`". -/
theorem eval_qG_iff_V (a : ℕ) (k : V) (X : Semiterm LAct Empty 1) (U W : ClosedSemiterm LAct 0)
    (X' : Semiterm LAct Empty 1) (U' W' : ClosedSemiterm LAct 0) {me opp : V}
    (hme : relabel (U.val (s := stdActV V) ![] Empty.elim) (W.val (s := stdActV V) ![] Empty.elim)
      (X.val (s := stdActV V) ![k] Empty.elim) = me)
    (hopp : relabel (U'.val (s := stdActV V) ![] Empty.elim) (W'.val (s := stdActV V) ![] Empty.elim)
      (X'.val (s := stdActV V) ![k] Empty.elim) = opp) :
    Semiformula.Eval (s := stdActV V) ![k] Empty.elim (qG a X U W X' U' W') ↔
      ∃ n, EvalGraph n opp me opp (a : V) := by
  unfold qG GtmplA Gtmpl
  rw [Semiformula.eval_substs, Semiformula.eval_substs, Semiformula.eval_lMap, stdActV_lMap_emb]
  have h0 : (Semiterm.val (s := stdActV V) ![k] Empty.elim ∘ ![X, cl U, cl W, X', cl U', cl W']) =
      ![X.val (s := stdActV V) ![k] Empty.elim, U.val (s := stdActV V) ![] Empty.elim,
        W.val (s := stdActV V) ![] Empty.elim, X'.val (s := stdActV V) ![k] Empty.elim,
        U'.val (s := stdActV V) ![] Empty.elim, W'.val (s := stdActV V) ![] Empty.elim] := by
    funext i; fin_cases i <;> simp [val_cl_V]
  rw [h0]
  have h1 : (Semiterm.val (s := stdActV V)
      ![X.val (s := stdActV V) ![k] Empty.elim, U.val (s := stdActV V) ![] Empty.elim,
        W.val (s := stdActV V) ![] Empty.elim, X'.val (s := stdActV V) ![k] Empty.elim,
        U'.val (s := stdActV V) ![] Empty.elim, W'.val (s := stdActV V) ![] Empty.elim]
      Empty.elim ∘ ![#0, #1, #2, #3, #4, #5, actT6 a]) =
      ![X.val (s := stdActV V) ![k] Empty.elim, U.val (s := stdActV V) ![] Empty.elim,
        W.val (s := stdActV V) ![] Empty.elim, X'.val (s := stdActV V) ![k] Empty.elim,
        U'.val (s := stdActV V) ![] Empty.elim, W'.val (s := stdActV V) ![] Empty.elim, (a : V)] := by
    funext i; fin_cases i <;> simp [val_actT6_V]
  rw [h1]
  refine (eval_gtmpl (V := V) _).trans ?_
  simp only [Matrix.cons_val]
  rw [hme, hopp]

/-! #### Cupod's guard against DIMCID, its transposition, and the mutual family -/

/-- **Cupod's guard against DIMCID**: `qCD(k)` says "`DimcidV k` plays D against `CupodV k`". -/
noncomputable def qCD : Semisentence LAct 1 := qG 1 TD uC wC TDi uDi wDi

lemma qCD_def : qCD = qG 1 TD uC wC TDi uDi wDi := rfl

/-- **The instance equation on codes**: Cupod's guard code against `DimcidV k`. -/
theorem guardCode_CupodV_DimcidV_eq_instB (k : V) :
    guardCode (⌜GtmplA 1⌝ : V) (CupodV k) (DimcidV k) = instB (⌜qCD⌝ : V) k :=
  guardCode_GtmplA_eq_instB 1 k TD uC wC TDi uDi wDi (hX_cupod k) (hU_cupod k) (hW_cupod k)
    (hX_self k) (hU_self k) (hW_self k)

/-- **The transposed instance equation**: Dupoc's guard code against `DimcidTV k` is the
`bnum k`-instance of `⌜lMap swap qCD⌝`. -/
theorem guardCode_DupocV_DimcidTV_eq_instB (k : V) :
    guardCode (⌜GtmplA 0⌝ : V) (DupocV k) (DimcidTV k) = instB (⌜Semiformula.lMap swap qCD⌝ : V) k := by
  have h := guardCode_GtmplA_swap_eq_instB 1 k TD uC wC TDi uDi wDi (hX_cupod k) (hU_cupod k) (hW_cupod k)
    (hX_self k) (hU_self k) (hW_self k)
  rwa [swapAct_one, swapcode_CupodV, swapcode_DimcidV] at h

/-- **The truth equation of `qCD` in every model** (standard reading). -/
theorem eval_qCD_iff_V (k : V) :
    Semiformula.Eval (s := stdActV V) ![k] Empty.elim qCD ↔
      ∃ n, EvalGraph n (DimcidV k) (CupodV k) (DimcidV k) 1 := by
  have h := eval_qG_iff_V 1 k TD uC wC TDi uDi wDi (hopp_cupod k) (hopp_self k)
  rwa [Nat.cast_one] at h

/-- **The truth equation of `lMap swap qCD` in every model** (standard reading): "`DimcidTV k` plays C
against `DupocV k`". -/
theorem eval_qCD_swapped_iff_V (k : V) :
    Semiformula.Eval (s := stdActV V) ![k] Empty.elim (Semiformula.lMap swap qCD) ↔
      ∃ n, EvalGraph n (DimcidTV k) (DupocV k) (DimcidTV k) 0 := by
  rw [qCD_def, lMap_swap_qG, swapAct_one]
  have h := eval_qG_iff_V 0 k _ _ _ _ _ _ (hopp'_cupod k) (hopp'_self k)
  rwa [Nat.cast_zero] at h

/-- The two-sided conjunct of the mutual family: Cupod's guard against DIMCID and its transposition. -/
noncomputable def pCD : Semisentence LAct 1 := qCD ⋏ Semiformula.lMap swap qCD

lemma pCD_def : pCD = qCD ⋏ Semiformula.lMap swap qCD := rfl

lemma lMap_swap_pCD : Semiformula.lMap swap pCD = Semiformula.lMap swap qCD ⋏ qCD := by
  rw [pCD_def, LogicalConnective.HomClass.map_and, lMap_swap_swap]

/-- **The MUTUAL Löb family of the DIMCID × Cupod cell**: DIMCID's family against Cupod's triple
(and the transposed searcher's against Dupoc's) AND Cupod's guard against DIMCID (and its
transposition) — four guards, each searcher's box supplied by the same conjunction. -/
noncomputable def pDC : Semisentence LAct 1 := pG TD uC wC ⋏ pCD

lemma pDC_def : pDC = pG TD uC wC ⋏ pCD := rfl

theorem instB_quote_pCD (k : V) :
    instB (⌜pCD⌝ : V) k = instB (⌜qCD⌝ : V) k ^⋏ instB (⌜Semiformula.lMap swap qCD⌝ : V) k :=
  instB_quote_and _ _ k

theorem instB_quote_pDC (k : V) :
    instB (⌜pDC⌝ : V) k = instB (⌜pG TD uC wC⌝ : V) k ^⋏ instB (⌜pCD⌝ : V) k :=
  instB_quote_and _ _ k

lemma formulaLen_instB_pCD (k : V) :
    formulaLen LAct (instB (⌜pCD⌝ : V) k) =
      formulaLen LAct (instB (⌜qCD⌝ : V) k) + formulaLen LAct (instB (⌜Semiformula.lMap swap qCD⌝ : V) k) + 1 := by
  rw [instB_quote_pCD,
    formulaLen_and (isFormula_instB_quote _ k).isUFormula (isFormula_instB_quote _ k).isUFormula]

lemma formulaLen_instB_pDC (k : V) :
    formulaLen LAct (instB (⌜pDC⌝ : V) k) =
      formulaLen LAct (instB (⌜pG TD uC wC⌝ : V) k) + formulaLen LAct (instB (⌜pCD⌝ : V) k) + 1 := by
  rw [instB_quote_pDC,
    formulaLen_and (isFormula_instB_quote _ k).isUFormula (isFormula_instB_quote _ k).isUFormula]

/-! #### The slack of a two-level ∧-elimination: `(14, 16)` -/

/-- Two ∧-eliminations (`8·(x+y)+7` then `8·(u+v)+7`, with `x = u + v + 1`) are below the family slack
`(14, 16)` at `z = x + y + 1` (for VARIABLE lengths, so that `push_cast` never sees a quote). -/
lemma slack4_le (a x y u v z : V) (hx : x = u + v + 1) (hz : z = x + y + 1) :
    a + 8 * (x + y) + 7 + 8 * (u + v) + 7 ≤ a + ((14 : ℕ) : V) + ((16 : ℕ) : V) * z := by
  have huv : u + v ≤ x + y := by subst hx; exact le_trans le_self_add le_self_add
  subst hz
  push_cast
  calc a + 8 * (x + y) + 7 + 8 * (u + v) + 7 ≤ a + 8 * (x + y) + 7 + 8 * (x + y) + 7 := by gcongr
    _ = a + 14 + 16 * (x + y) := by ring
    _ ≤ a + 14 + 16 * (x + y + 1) := by gcongr a + 14 + 16 * ?_; exact le_self_add

/-- The same with the inner conjunction on the RIGHT (`y = u + v + 1`). -/
lemma slack4_le' (a x y u v z : V) (hy : y = u + v + 1) (hz : z = x + y + 1) :
    a + 8 * (x + y) + 7 + 8 * (u + v) + 7 ≤ a + ((14 : ℕ) : V) + ((16 : ℕ) : V) * z := by
  have huv : u + v ≤ x + y := by subst hy; exact le_trans le_self_add le_add_self
  subst hz
  push_cast
  calc a + 8 * (x + y) + 7 + 8 * (u + v) + 7 ≤ a + 8 * (x + y) + 7 + 8 * (x + y) + 7 := by gcongr
    _ = a + 14 + 16 * (x + y) := by ring
    _ ≤ a + 14 + 16 * (x + y + 1) := by gcongr a + 14 + 16 * ?_; exact le_self_add

/-- The same at `ℕ`, in the `le_def` shape. -/
lemma slack4_nat (a x y u v z k : ℕ) (hx : x = u + v + 1) (hz : z = x + y + 1) (h : a + 14 + 16 * z ≤ k) :
    a + 8 * (x + y) + 7 + 8 * (u + v) + 7 = k ∨ a + 8 * (x + y) + 7 + 8 * (u + v) + 7 < k := by
  subst hx hz; omega

lemma slack4_nat' (a x y u v z k : ℕ) (hy : y = u + v + 1) (hz : z = x + y + 1) (h : a + 14 + 16 * z ≤ k) :
    a + 8 * (x + y) + 7 + 8 * (u + v) + 7 = k ∨ a + 8 * (x + y) + 7 + 8 * (u + v) + 7 < k := by
  subst hy hz; omega

/-- **All four searchers find their guards from a box of the mutual family** (fuel 2): DIMCID defects
against Cupod, the transposed searcher cooperates with Dupoc, Cupod defects against DIMCID, Dupoc
cooperates with the transposed searcher. -/
theorem pDC_all_V (k a : V)
    (ha₁ : a + 8 * (formulaLen LAct (instB (⌜pG TD uC wC⌝ : V) k) + formulaLen LAct (instB (⌜pCD⌝ : V) k)) + 7 +
      8 * (formulaLen LAct (instB (⌜qDG TD uC wC⌝ : V) k) +
        formulaLen LAct (instB (⌜qTG (Semiterm.lMap swap TD) (Semiterm.lMap swap uC) (Semiterm.lMap swap wC)⌝ : V) k))
      + 7 ≤ k)
    (ha₂ : a + 8 * (formulaLen LAct (instB (⌜pG TD uC wC⌝ : V) k) + formulaLen LAct (instB (⌜pCD⌝ : V) k)) + 7 +
      8 * (formulaLen LAct (instB (⌜qCD⌝ : V) k) + formulaLen LAct (instB (⌜Semiformula.lMap swap qCD⌝ : V) k))
      + 7 ≤ k)
    (h : LenDerivable TAct a (instB (⌜pDC⌝ : V) k)) :
    (EvalGraph 2 (DimcidV k) (CupodV k) (DimcidV k) 1 ∧ EvalGraph 2 (DimcidTV k) (DupocV k) (DimcidTV k) 0) ∧
    (EvalGraph 2 (CupodV k) (DimcidV k) (CupodV k) 1 ∧ EvalGraph 2 (DupocV k) (DimcidTV k) (DupocV k) 0) := by
  rw [instB_quote_pDC] at h
  have hx := isFormula_instB_quote (pG TD uC wC) k
  have hy := isFormula_instB_quote pCD k
  have h₁ := lenDerivable_andL_V hx hy h
  have h₂ := lenDerivable_andR_V hx hy h
  obtain ⟨g1, g2⟩ := pG_both_V k TD uC wC (hX_cupod k) (hU_cupod k) (hW_cupod k) _ ha₁ h₁
  rw [swapcode_CupodV] at g2
  have hx' := isFormula_instB_quote qCD k
  have hy' := isFormula_instB_quote (Semiformula.lMap swap qCD) k
  have h₂' : LenDerivable TAct
      (a + 8 * (formulaLen LAct (instB (⌜pG TD uC wC⌝ : V) k) + formulaLen LAct (instB (⌜pCD⌝ : V) k)) + 7)
      (instB (⌜qCD⌝ : V) k ^⋏ instB (⌜Semiformula.lMap swap qCD⌝ : V) k) := by
    rw [← instB_quote_pCD]; exact h₂
  have c1 := lenDerivable_mono_V ha₂ (lenDerivable_andL_V hx' hy' h₂')
  have c2 := lenDerivable_mono_V ha₂ (lenDerivable_andR_V hx' hy' h₂')
  rw [lenDerivable_iff_lenProvableV, ← guardCode_CupodV_DimcidV_eq_instB] at c1
  rw [lenDerivable_iff_lenProvableV, ← guardCode_DupocV_DimcidTV_eq_instB] at c2
  exact ⟨⟨g1, g2⟩, ⟨cupod_search_any_V k _ c1, dupoc_search_any_V k _ c2⟩⟩

/-- **The box form**: the two guards of the cell are provable within `k`. -/
theorem pDC_guards_V (k a : V)
    (ha₁ : a + 8 * (formulaLen LAct (instB (⌜pG TD uC wC⌝ : V) k) + formulaLen LAct (instB (⌜pCD⌝ : V) k)) + 7 +
      8 * (formulaLen LAct (instB (⌜qDG TD uC wC⌝ : V) k) +
        formulaLen LAct (instB (⌜qTG (Semiterm.lMap swap TD) (Semiterm.lMap swap uC) (Semiterm.lMap swap wC)⌝ : V) k))
      + 7 ≤ k)
    (ha₂ : a + 8 * (formulaLen LAct (instB (⌜pG TD uC wC⌝ : V) k) + formulaLen LAct (instB (⌜pCD⌝ : V) k)) + 7 +
      8 * (formulaLen LAct (instB (⌜qCD⌝ : V) k) + formulaLen LAct (instB (⌜Semiformula.lMap swap qCD⌝ : V) k))
      + 7 ≤ k)
    (h : LenDerivable TAct a (instB (⌜pDC⌝ : V) k)) :
    LenProvableV TAct k (guardCode (⌜tmplD⌝ : V) (DimcidV k) (CupodV k)) ∧
    LenProvableV TAct k (guardCode (⌜GtmplA 1⌝ : V) (CupodV k) (DimcidV k)) := by
  rw [instB_quote_pDC] at h
  have hx := isFormula_instB_quote (pG TD uC wC) k
  have hy := isFormula_instB_quote pCD k
  have h₁ := lenDerivable_andL_V hx hy h
  have h₂ := lenDerivable_andR_V hx hy h
  obtain ⟨g1, _⟩ := pG_guards_V k TD uC wC (hX_cupod k) (hU_cupod k) (hW_cupod k) _ ha₁ h₁
  have hx' := isFormula_instB_quote qCD k
  have hy' := isFormula_instB_quote (Semiformula.lMap swap qCD) k
  have h₂' : LenDerivable TAct
      (a + 8 * (formulaLen LAct (instB (⌜pG TD uC wC⌝ : V) k) + formulaLen LAct (instB (⌜pCD⌝ : V) k)) + 7)
      (instB (⌜qCD⌝ : V) k ^⋏ instB (⌜Semiformula.lMap swap qCD⌝ : V) k) := by
    rw [← instB_quote_pCD]; exact h₂
  have c1 := lenDerivable_mono_V ha₂ (lenDerivable_andL_V hx' hy' h₂')
  rw [lenDerivable_iff_lenProvableV, ← guardCode_CupodV_DimcidV_eq_instB] at c1
  exact ⟨g1, c1⟩

/-! #### `pDC` in both readings -/

/-- `pDC(k)` in the standard reading. -/
theorem eval_pDC_iff_std (k : V) :
    Semiformula.Eval (s := stdActV V) ![k] Empty.elim pDC ↔
      (((∃ n, EvalGraph n (DimcidV k) (CupodV k) (DimcidV k) 0) → (∃ n, EvalGraph n (CupodV k) (DimcidV k) (CupodV k) 1)) ∧
       ((∃ n, EvalGraph n (DimcidTV k) (DupocV k) (DimcidTV k) 1) → (∃ n, EvalGraph n (DupocV k) (DimcidTV k) (DupocV k) 0))) ∧
      ((∃ n, EvalGraph n (DimcidV k) (CupodV k) (DimcidV k) 1) ∧ (∃ n, EvalGraph n (DimcidTV k) (DupocV k) (DimcidTV k) 0)) := by
  rw [pDC_def, pCD_def]
  simp only [LogicalConnective.HomClass.map_and, LogicalConnective.Prop.and_eq]
  rw [eval_pG_iff_std k TD uC wC (hopp_cupod k) (hopp'_cupod k), eval_qCD_iff_V, eval_qCD_swapped_iff_V]

/-- `pDC(k)` in the swapped reading: the SAME content (the conjuncts exchange roles). -/
theorem eval_pDC_iff_swap (k : V) :
    Semiformula.Eval (s := swapActS V) ![k] Empty.elim pDC ↔
      (((∃ n, EvalGraph n (DimcidV k) (CupodV k) (DimcidV k) 0) → (∃ n, EvalGraph n (CupodV k) (DimcidV k) (CupodV k) 1)) ∧
       ((∃ n, EvalGraph n (DimcidTV k) (DupocV k) (DimcidTV k) 1) → (∃ n, EvalGraph n (DupocV k) (DimcidTV k) (DupocV k) 0))) ∧
      ((∃ n, EvalGraph n (DimcidV k) (CupodV k) (DimcidV k) 1) ∧ (∃ n, EvalGraph n (DimcidTV k) (DupocV k) (DimcidTV k) 0)) := by
  rw [eval_swapActS, pDC_def, LogicalConnective.HomClass.map_and, lMap_swap_pG, lMap_swap_pCD, ← stdActV_eq_stdActS]
  simp only [LogicalConnective.HomClass.map_and, LogicalConnective.Prop.and_eq]
  rw [eval_qDG_iff_V k TD uC wC (hopp_cupod k), eval_qTG_iff_V k _ _ _ (hopp'_cupod k), eval_qCD_iff_V,
    eval_qCD_swapped_iff_V, and_comm (a := ∃ n, EvalGraph n (DimcidTV k) (DupocV k) (DimcidTV k) 0),
    and_comm (a := (∃ n, EvalGraph n (DimcidTV k) (DupocV k) (DimcidTV k) 1) → _)]

theorem eval_pDC_iff_stdActS (k : V) :
    Semiformula.Eval (s := stdActS V) ![k] Empty.elim pDC ↔
      (((∃ n, EvalGraph n (DimcidV k) (CupodV k) (DimcidV k) 0) → (∃ n, EvalGraph n (CupodV k) (DimcidV k) (CupodV k) 1)) ∧
       ((∃ n, EvalGraph n (DimcidTV k) (DupocV k) (DimcidTV k) 1) → (∃ n, EvalGraph n (DupocV k) (DimcidTV k) (DupocV k) 0))) ∧
      ((∃ n, EvalGraph n (DimcidV k) (CupodV k) (DimcidV k) 1) ∧ (∃ n, EvalGraph n (DimcidTV k) (DupocV k) (DimcidTV k) 0)) := by
  rw [← stdActV_eq_stdActS]; exact eval_pDC_iff_std k

/-! #### The Löb premise and the cells -/

/-- **The bounded Löb premise of the mutual family, slack `(14, 16)`**: a box of `pDC(k)` makes all four
searchers find their guards (fuel 2); DIMCID's implications hold because Cupod/Dupoc actually play the
consequents, and Cupod's/Dupoc's guards are the plays of DIMCID/its transposition — true in both
readings. -/
theorem loebSound_pDC : LoebSound pDC 14 16 := by
  intro V _ _ k a ha h
  have : V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁ := inferInstance
  have ha₁ := le_trans (slack4_le a _ _ _ _ _ (formulaLen_instB_pG TD uC wC k) (formulaLen_instB_pDC k)) ha
  have ha₂ := le_trans (slack4_le' a _ _ _ _ _ (formulaLen_instB_pCD k) (formulaLen_instB_pDC k)) ha
  obtain ⟨⟨g1, g2⟩, ⟨c1, c2⟩⟩ := pDC_all_V k a ha₁ ha₂ h
  exact ⟨(eval_pDC_iff_stdActS k).mpr ⟨⟨fun _ ↦ ⟨2, c1⟩, fun _ ↦ ⟨2, c2⟩⟩, ⟨⟨2, g1⟩, ⟨2, g2⟩⟩⟩,
    (eval_pDC_iff_swap k).mpr ⟨⟨fun _ ↦ ⟨2, c1⟩, fun _ ↦ ⟨2, c2⟩⟩, ⟨⟨2, g1⟩, ⟨2, g2⟩⟩⟩⟩

/-- **The DIMCID × Cupod cell, packaged**: for all large `k`, DIMCID defects against Cupod and Cupod
defects against DIMCID (fuel 2), and both guard boxes hold. -/
theorem dimcid_cupod_cell_core {d : ℕ} (hE : BoundedInnerNec d) :
    ∃ k₀ : ℕ, ∀ k : ℕ, k₀ < k →
      (EvalGraph 2 (Dimcid k) (Cupod k) (Dimcid k) 1 ∧ EvalGraph 2 (Cupod k) (Dimcid k) (Cupod k) 1) ∧
      (LenProvableV TAct k (guardCode (⌜tmplD⌝ : ℕ) (Dimcid k) (Cupod k)) ∧
        LenProvableV TAct k (guardCode (⌜GtmplA 1⌝ : ℕ) (Cupod k) (Dimcid k))) := by
  obtain ⟨k₀, h⟩ := family_found pDC hE loebSound_pDC
  refine ⟨k₀, fun k hk ↦ ?_⟩
  obtain ⟨a, ha, hpc⟩ := h k hk
  have ha₁ := le_def.mpr (slack4_nat a _ _ _ _ _ k (formulaLen_instB_pG (V := ℕ) TD uC wC k)
    (formulaLen_instB_pDC (V := ℕ) k) ha)
  have ha₂ := le_def.mpr (slack4_nat' a _ _ _ _ _ k (formulaLen_instB_pCD (V := ℕ) k)
    (formulaLen_instB_pDC (V := ℕ) k) ha)
  obtain ⟨⟨g1, _⟩, ⟨c1, _⟩⟩ := pDC_all_V (V := ℕ) k a ha₁ ha₂ hpc
  exact ⟨⟨g1, c1⟩, pDC_guards_V (V := ℕ) k a ha₁ ha₂ hpc⟩

/-- **DIMCID × Cupod is `(D, D)` in PA-`S'`, conditional on bounded inner necessitation**: for all
large `k`, `Dimcid k` defects against `Cupod k` and `Cupod k` defects against `Dimcid k` (fuel 2). -/
theorem dimcid_cupod_defect {d : ℕ} (hE : BoundedInnerNec d) :
    ∃ k₀ : ℕ, ∀ k : ℕ, k₀ < k →
      EvalGraph 2 (Dimcid k) (Cupod k) (Dimcid k) 1 ∧ EvalGraph 2 (Cupod k) (Dimcid k) (Cupod k) 1 := by
  obtain ⟨k₀, h⟩ := dimcid_cupod_cell_core hE
  exact ⟨k₀, fun k hk ↦ (h k hk).1⟩

/-- **The box form**: for all large `k`, both DIMCID and Cupod FIND their guards against each other
within the budget `k` (conditional). -/
theorem dimcid_cupod_find_guards {d : ℕ} (hE : BoundedInnerNec d) :
    ∃ k₀ : ℕ, ∀ k : ℕ, k₀ < k →
      LenProvableV TAct k (guardCode (⌜tmplD⌝ : ℕ) (Dimcid k) (Cupod k)) ∧
      LenProvableV TAct k (guardCode (⌜GtmplA 1⌝ : ℕ) (Cupod k) (Dimcid k)) := by
  obtain ⟨k₀, h⟩ := dimcid_cupod_cell_core hE
  exact ⟨k₀, fun k hk ↦ (h k hk).2⟩

/-- **DIMCID × Cupod `(D, D)` in PA-`S'`, unconditional.** -/
theorem dimcid_cupod_defect_unconditional :
    ∃ k₀ : ℕ, ∀ k : ℕ, k₀ < k →
      EvalGraph 2 (Dimcid k) (Cupod k) (Dimcid k) 1 ∧ EvalGraph 2 (Cupod k) (Dimcid k) (Cupod k) 1 :=
  dimcid_cupod_defect boundedInnerNec_sixteen

/-- **DIMCID and Cupod find their guards against each other, unconditional.** -/
theorem dimcid_cupod_find_guards_unconditional :
    ∃ k₀ : ℕ, ∀ k : ℕ, k₀ < k →
      LenProvableV TAct k (guardCode (⌜tmplD⌝ : ℕ) (Dimcid k) (Cupod k)) ∧
      LenProvableV TAct k (guardCode (⌜GtmplA 1⌝ : ℕ) (Cupod k) (Dimcid k)) :=
  dimcid_cupod_find_guards boundedInnerNec_sixteen

end cupodCell

end ArithS
