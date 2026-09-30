import ArithS.Audit.RedCellInstance
import ArithS.Audit.RedCellUnsound
import ArithS.Cells.SimSlot
import ArithS.Cells.PrudentLoose
import ArithS.Cells.DupocEngine
import ArithS.Cells.DimcidEngine
import ArithS.Cells.CimcicEngine
import PrisonersDilemma.Theorems.DupocBot.RedCellInstance

/-!
# ArithS.Audit.Cells — the axiom census of the arithmetized layer: Cells

This file covers the cells (`Cells/`): T1, the red cell, with its audit twins
(`Audit/RedCellUnsound`, `Audit/RedCellInstance`, `Agents/Fit`), then the route-B matrix — the
common substrate, the Löbian families, the search-free/SND/POS classes, the flips, the floors.

Split out of the former single `ArithS/Audit.lean` on 2026-09-28; every `#print axioms` line and its
comment block are verbatim (the comment blocks are the historical record). `ArithS/Audit.lean` imports
the nine per-layer files; each line must read `[propext, Classical.choice, Quot.sound]`.
-/

namespace ArithS

-- T1: the red cell, at every shared budget, fuel 2; and its non-vacuity.
example : ∀ k : ℕ, EvalGraph 2 (Dupoc k) (Cupod k) (Dupoc k) 1 ∧ EvalGraph 2 (Cupod k) (Dupoc k) (Cupod k) 0 :=
  red_cell
#print axioms red_cell
#print axioms red_cell_unique
-- The red cell ONCE, abstractly (`Base/RedCellFramework`: symmetry excludes (C,C)/(D,D),
-- soundness excludes (C,D)), and its two instances: the engine's `Pf` and PA-`S'`.
#print axioms PD.RedCellFramework.red_cell
#print axioms PD.Theorems.red_cell_engine
#print axioms red_cell_via_framework
#print axioms guard_fits
#print axioms guard_fits'
-- The audit's "drop soundness" mutation as a THEOREM (`RedCellUnsound`, Proposition 6.1):
-- `TBad = TAct + {c_C = c_D}` is inconsistent, every sentence has a `TBad`-proof of length
-- `3|φ| + 2|axEq| + 3`, both guards are found for all large `k`, and under the evaluator
-- consulting `TBad` (a verbatim copy with the theory swapped) the cell FLIPS to `(C, D)`.
#print axioms tbad_inconsistent
#print axioms lenBoxNat_TBad_of_formulaLenMeta
#print axioms guard_provable_bad
#print axioms red_cell_flips_when_unsound
#print axioms red_cell_flip
#print axioms red_cell_flips_unique

-- Consolidation stage 1 (Cells/Common/Syntax, 2026-09-24): the arity-generic syntax lemmas shared by every
-- cell file, MOVED out of JustSlot/DIMCID/JustBot/PrudentMirror/DimcidFlips/DupocMirror/PositiveCells unchanged
-- (names, statements, proofs). Only the names not already printed by the blocks below.
#print axioms semiterm_quote_emb_n
#print axioms semiterm_quote_emb₄
#print axioms semiterm_quote_emb₇
#print axioms isSemiformula_quote₄
#print axioms isSemiformula_quote₇
#print axioms four_eq
#print axioms coe_quote_sentence₆
#print axioms revalueTemplate_quote_sentence₆_V
#print axioms nth_descriptions_three
#print axioms nth_descriptions_four
#print axioms nth_descriptions_five
#print axioms nth_descriptionsB_zero
#print axioms nth_descriptionsB_one
#print axioms nth_descriptionsB_two
#print axioms nth_descriptionsB_three
#print axioms nth_descriptionsB_four
#print axioms nth_descriptionsB_five
#print axioms nth_descriptionsB_six
#print axioms coe_quote_sentence₇
#print axioms quote_emb_numT
#print axioms pBot_le_pBot_iff
#print axioms pBot_lt_pBot_iff
#print axioms transposeCode_pBot
#print axioms revalueU_pBot
#print axioms revalueW_pBot
#print axioms transposeCode_pBot_DupocV
#print axioms pConst_zero_lt_one
#print axioms transposeCode_pConst_zero
#print axioms transposeCode_pConst_one
#print axioms revalueU_pConst_zero
#print axioms revalueW_pConst_zero
#print axioms revalueU_pConst_one
#print axioms revalueW_pConst_one

-- Consolidation stage 2 (Cells/Common/Bots, 2026-09-24): Mirror/TM, the Tft block and FlipCells' TFTV twins (now
-- one-liners over it: TFTV_eq_TftV/TFTTV_eq_TftTV/TTFT_eq_TTft), T0/TB0, the generic searcher SV with its
-- variable block, gDu/gCu/gW/gWT, TBS — MOVED unchanged; plus the NEW bridges DimcidV_eq_SV/CimcicV_eq_SV
-- (Cells/DIMCID, Cells/CIMCIC). Only the names not already printed elsewhere.
#print axioms MirrorV_nat
#print axioms cast_Mirror
#print axioms transposeCode_MirrorV
#print axioms canonical_MirrorV
#print axioms revalueU_MirrorV
#print axioms revalueW_MirrorV
#print axioms lMap_swap_TM
#print axioms val_TM_V
#print axioms quote_emb_TM
#print axioms progCode_TFT
#print axioms TftV_nat
#print axioms cast_Tft
#print axioms transposeCode_TftV
#print axioms transposeCode_TftTV
#print axioms canonical_TftV
#print axioms revalueU_TftV
#print axioms revalueW_TftV
#print axioms lMap_swap_TTft
#print axioms val_TTft_V
#print axioms quote_emb_TTft
#print axioms hX_tft
#print axioms hU_tft
#print axioms hW_tft
#print axioms val_desc_tft_swap
#print axioms TFTV_eq_TftV
#print axioms TFTTV_eq_TftTV
#print axioms cast_TFT
#print axioms TFTV_nat
#print axioms transposeCode_TFTV
#print axioms canonical_TFTV
#print axioms revalueU_TFTV
#print axioms revalueW_TFTV
#print axioms TTFT_eq_TTft
#print axioms lMap_swap_TTFT
#print axioms val_TTFT_V
#print axioms quote_emb_TTFT
#print axioms lMap_swap_T0
#print axioms val_T0_V
#print axioms quote_emb_T0
#print axioms lMap_swap_TB0
#print axioms val_TB0_V
#print axioms quote_emb_TB0
#print axioms hU_C_zero
#print axioms hW_D_zero
#print axioms hU_D_one
#print axioms hW_C_one
#print axioms hU_C_bot_zero
#print axioms hW_D_bot_zero
#print axioms hU_D_bot_one
#print axioms hW_C_bot_one
#print axioms val_desc_bot_zero
#print axioms val_desc_bot_one
#print axioms SV_nat
#print axioms innerS_def
#print axioms cast_innerS
#print axioms SV_eq_inner
#print axioms swapAction_cast
#print axioms swapAction_cast'
#print axioms one_sub_one_sub
#print axioms SV_lt_SVT_iff
#print axioms SVT_lt_SV_iff
#print axioms SV_eq_cast
#print axioms SVT_eq_cast
#print axioms lMap_swap_TS
#print axioms quote_emb_TS
#print axioms hU_SV
#print axioms hW_SV
#print axioms val_botT1_V
#print axioms quote_emb_botT1
#print axioms lMap_swap_gDu
#print axioms lMap_swap_gCu
#print axioms lMap_swap_gW
#print axioms lMap_swap_TBS
#print axioms val_TBS_V
#print axioms quote_emb_TBS
#print axioms hU_botSV
#print axioms hW_botSV
#print axioms DimcidV_eq_SV
#print axioms DimcidTV_eq_SV
#print axioms CimcicV_eq_SV
#print axioms CimcicTV_eq_SV

-- Consolidation stage 3 (Cells/Common/Templates, 2026-09-24): qG/gVec, qT, JustBot's templateVec form (templateVec_eq_gVec
-- NEW, rfl), the atom truths, the Dupoc towers (TD/TBD description hypotheses) and the Describes layer
-- (descVal/Describes/DescribesAbove, describes_closed and the instances) — MOVED unchanged. Only the names not
-- already printed elsewhere.
#print axioms lMap_swap_qG
#print axioms semitermVec_val_gVec
#print axioms quote_qG
#print axioms gVec_semitermVec
#print axioms termSubstVec_gVec
#print axioms lMap_swap_qT
#print axioms quote_qT
#print axioms quote_GtmplA_subst
#print axioms templateVec_semitermVec
#print axioms termSubstVec_templateVec
#print axioms templateVec_eq_gVec
#print axioms transposeCode_CupodV
#print axioms canonical_CupodV_eq
#print axioms hX_cupod
#print axioms hU_cupod
#print axioms hW_cupod
#print axioms desc_cupod
#print axioms descT_cupod
#print axioms hX_dupoc
#print axioms hU_dupoc
#print axioms hW_dupoc
#print axioms lMap_swap_TBD
#print axioms quote_emb_TBD
#print axioms quote_emb_uD_botDupocV
#print axioms quote_emb_wD_botDupocV
#print axioms hX_botDupoc
#print axioms hU_botDupoc
#print axioms hW_botDupoc
#print axioms descVal_def
#print axioms lMap_swap_canonicalMeta'
#print axioms descVal_botCB
#print axioms descVal_botCB_T
#print axioms descVal_TFT
#print axioms descVal_TFT_T
#print axioms descVal_SV
#print axioms descVal_SV_T
#print axioms descVal_botSV
#print axioms descVal_botSV_T
#print axioms descVal_dupocV
#print axioms descVal_dupocV_T
#print axioms descVal_botDupoc
#print axioms descVal_botDupoc_T

-- Consolidation stage 4 (Cells/Common/Probers, 2026-09-24): the search clauses in any frame, Mirror's step and
-- copies, TFT's probe steps, the constants — MOVED unchanged; NEW roots search_then_V₆/search_else_V₆ (the two
-- directions of EvalGraph.search_iff₆). Only the names not already printed elsewhere.
#print axioms search_then_V₆
#print axioms search_else_V₆
#print axioms botSV_then_V
#print axioms cupod_frame_search_V
#print axioms botCupod_frame_search_V
#print axioms cupod_search_any_V
#print axioms dupoc_search_any_V
#print axioms mirror_copies2_V
#print axioms mirror_copies3_V
#print axioms tftT_D_of_probe_D_V
#print axioms const_play_V
#print axioms bot_const_play_V
#print axioms const_not_play_V
#print axioms bot_const_not_play_V

-- Consolidation stage 5 (Cells/Common/Families, 2026-09-24): the family pQ q := q ⋏ τq and its lemmas (MOVED from
-- FlipCells), nat_le_of_le_def (MOVED), NEW loebSound_pQ_of (loebSound_pWM/pWW are corollaries) and NEW
-- slack_depth_le (slack4_*/slack6_* are corollaries, in place); loebSound_pG_of/_of_above moved into DIMCID after
-- pG with the NEW describes_dimcid/describes_mirror (DIMCID) and describes_CB (Common/Templates) making
-- loebSound_pDD/_pDMi/_pDi0 corollaries. Only the names not already printed elsewhere.
#print axioms instB_quote_pQ
#print axioms formulaLen_instB_pQ
#print axioms eval_pQ_std
#print axioms eval_pQ_swap
#print axioms loebSound_pQ_of
#print axioms slack_depth_le
#print axioms describes_CB
#print axioms describes_dimcid
#print axioms describes_mirror

-- Consolidation stage 6 (Cells/Common/Khat, 2026-09-24): the k̂-chain — linear_size_le_eventually (ex-CIMCIC),
-- tact_all_of_both/found_of_all (ex-PositiveCells; pos_Cimcic_vs_Cimcic_guard is now found_of_all tact_proves_qCC),
-- found_of_all_V/tact_all_above_of_both/exists_instance_length_above/found_of_all_above (ex-KhatCells), BoxConseq
-- & co (ex-FlipCells) — MOVED unchanged. Only the theorems not already printed elsewhere.

-- Route B Phase 2, cell 1 — Dupoc × Mirror `(C, C)` and Cupod × Mirror `(D, D)` in PA-`S'` (Cells/DupocMirror,
-- 2026-09-23), the first Löb family after self-play, on the family-parametric assembly: Mirror in every model
-- (`MirrorV = pSim pOpp pSelf`, τ-fixed, closed description; the sim step `mirror_step_V`), the guards as
-- `k`-instances of the FIXED formulas `qDM`/`qCM = lMap swap qDM` (instance equations on codes in every model,
-- nothing in `Instance*`/`Guard`/`Template` generalized), the truth equations in both readings ("Mirror plays C
-- against Dupoc k" / "D against Cupod k"), the search clauses at fuel 2, the conjunction family `pDM = qDM ⋏ qCM`
-- (∧-elimination on codes: both searchers find their guards; Mirror COPIES at fuel 3), `loebSound_pDM :
-- LoebSound pDM 7 8`, and the cells from `family_found pDM`: conditional on `BoundedInnerNec d`, then
-- UNCONDITIONAL at `boundedInnerNec_sixteen` — for all large `k`, `Dupoc k` cooperates with Mirror and Mirror
-- copies (`(C, C)`), `Cupod k` defects against Mirror and Mirror copies (`(D, D)`), and both FIND their guards.
#print axioms mirror_step_V
#print axioms guardCode_DupocV_MirrorV_eq_instB
#print axioms guardCode_CupodV_MirrorV_eq_instB
#print axioms eval_qDM_iff_V
#print axioms eval_qCM_iff_V
#print axioms eval_qDM_swap_iff_V
#print axioms eval_qCM_swap_iff_V
#print axioms dupoc_mirror_search_V
#print axioms cupod_mirror_search_V
#print axioms instB_quote_pDM
#print axioms pDM_both_V
#print axioms pDM_guards_V
#print axioms eval_pDM_iff_std
#print axioms eval_pDM_iff_swap
#print axioms loebSound_pDM
#print axioms loeb_Dupoc_vs_Mirror_core_of_nec
#print axioms loeb_Dupoc_vs_Mirror_of_nec
#print axioms loeb_Cupod_vs_Mirror_of_nec
#print axioms loeb_Dupoc_vs_Mirror_guard_of_nec
#print axioms loeb_Cupod_vs_Mirror_guard_of_nec
#print axioms loeb_Dupoc_vs_Mirror
#print axioms loeb_Cupod_vs_Mirror

-- Cells/DupocEngine — the same four Löb cells on the ENGINE's codes `progCode (DupocBot k)` /
-- `progCode (CupodBot k)` (`SV gDu 0` / `SV gCu 1`), via the two-guard family `pQ` and `family_found`;
-- retires the hand-twin `outcome_Dupoc_vs_Dupoc`/`_MirrorBot` and `outcome_Cupod_vs_*` statements.
#print axioms loeb_DupocBot_vs_DupocBot
#print axioms loeb_CupodBot_vs_CupodBot
#print axioms loeb_DupocBot_vs_MirrorBot
#print axioms loeb_CupodBot_vs_MirrorBot
#print axioms loeb_DupocBot_vs_DupocBot_guard
#print axioms loeb_CupodBot_vs_CupodBot_guard
#print axioms loeb_DupocBot_vs_MirrorBot_guard
#print axioms loeb_CupodBot_vs_MirrorBot_guard

-- Cells/DimcidEngine — DIMCID × Cupod on the ENGINE's `progCode (CupodBot k)` (= `SV gCu 1`), the
-- mutual family of `Cells/DIMCID.lean` §9 re-run on the generic searcher; retires `outcome_DIMCID_vs_Cupod`.
#print axioms loeb_DIMCID_vs_CupodBot
#print axioms loeb_DIMCID_vs_CupodBot_guards

-- Cells/CimcicEngine — CIMCIC × Dupoc on the ENGINE's `progCode (DupocBot k)` (= `SV gDu 0`), the mutual
-- family of `Cells/CIMCIC.lean` §7 re-run on the generic searcher; retires `outcome_CIMCIC_vs_Dupoc`.
#print axioms loeb_CIMCIC_vs_DupocBot
#print axioms loeb_CIMCIC_vs_DupocBot_guards
#print axioms loebSound_pCiDb
#print axioms loeb_Dupoc_vs_Mirror_guard
#print axioms loeb_Cupod_vs_Mirror_guard

-- Route B Phase 2, the DIMCID family — DIMCID × DIMCID, DIMCID × Mirror and DIMCID × Cupod, all `(D, D)`, in
-- PA-`S'` (Cells/DIMCID, 2026-09-23), the first family whose guard is the GENERAL translation `template` (an `.impl` of two
-- pronoun atoms, `templateD := template phiD`, a closed constant never evaluated; `progCode (PD.Bots.DIMCID k) = Dimcid k`).
-- New: the truth of `template` at the PRONOUN atoms `.plays .self .opp a` / `.plays .opp .self a` in every model
-- (`eval_template_plays_self_opp_V`/`_opp_self_V` — `Det.models_sentenceAt_plays_V` covers only PROPER programs), hence
-- `eval_templateD_V`. The fixed formulas are generic in the opponent's description triple (`qDG`/`qTG`, the family
-- `pG X U W = qDG X U W ⋏ qTG (swap X) (swap U) (swap W)`); the instance equations on codes take the three
-- code-level description hypotheses; `pG_both_V` is the ∧-elimination. Löb: a box of the family makes DIMCID
-- DEFECT, which makes each guard's consequent ("opp plays D against me") true — against itself at fuel 2,
-- against Mirror by the copy at fuel 3 — so the implications hold in both readings (`loebSound_pDD`,
-- `loebSound_pDMi : LoebSound _ 7 8`), and `family_found` gives the cells: conditional on `BoundedInnerNec d`,
-- then UNCONDITIONAL at `boundedInnerNec_sixteen`. Nothing in `Code`/`Agent`/`Det`/`Instance*` was changed.
#print axioms progCode_DIMCID
#print axioms transposeCode_DimcidV
#print axioms canonical_DimcidV
#print axioms eval_template_plays_self_opp_V
#print axioms eval_template_plays_opp_self_V
#print axioms eval_templateD_V
#print axioms eval_qDG_iff_V
#print axioms eval_qTG_iff_V
#print axioms guardCode_DimcidV_eq_instB
#print axioms guardCode_DimcidTV_eq_instB
#print axioms dimcid_search_V
#print axioms pG_both_V
#print axioms pG_guards_V
#print axioms eval_pG_iff_std
#print axioms eval_pG_iff_swap
#print axioms guardCode_DimcidV_self_eq_instB
#print axioms eval_qDD_iff_V
#print axioms eval_qDD_swap_iff_V
#print axioms loebSound_pDD
#print axioms loeb_Dimcid_vs_Dimcid_core_of_nec
#print axioms loeb_Dimcid_vs_Dimcid_of_nec
#print axioms loeb_Dimcid_vs_Dimcid_guard_of_nec
#print axioms loeb_Dimcid_vs_Dimcid
#print axioms loeb_Dimcid_vs_Dimcid_guard
#print axioms loeb_DIMCID_vs_DIMCID_guardOf
#print axioms guardCode_DimcidV_MirrorV_eq_instB
#print axioms eval_qDMi_iff_V
#print axioms eval_qDMi_swap_iff_V
#print axioms loebSound_pDMi
#print axioms loeb_Dimcid_vs_Mirror_core_of_nec
#print axioms loeb_Dimcid_vs_Mirror_of_nec
#print axioms loeb_Dimcid_vs_Mirror_guard_of_nec
#print axioms loeb_Dimcid_vs_Mirror
#print axioms loeb_Dimcid_vs_Mirror_guard
-- Cell 3, the MUTUAL family DIMCID × Cupod `(D, D)` (engine `mutual_pblt_engine_id`): Cupod's description
-- (`revalueU_CupodV`/`revalueW_CupodV`), the hand-written template filled with two arbitrary triples (`qG`, the generic
-- `guardCode_GtmplA_eq_instB`/`_swap_eq_instB`, `eval_qG_iff_V`), Cupod's guard against DIMCID `qCD`, the four-guard
-- family `pDC = pG TD uC wC ⋏ (qCD ⋏ τqCD)` with the two-level ∧-elimination at slack `(14, 16)` (`pDC_all_V`),
-- `loebSound_pDC : LoebSound pDC 14 16`, then the cell: both defect at fuel 2, both find their guards.
#print axioms revalueU_CupodV
#print axioms revalueW_CupodV
#print axioms guardCode_GtmplA_eq_instB
#print axioms guardCode_GtmplA_swap_eq_instB
#print axioms eval_qG_iff_V
#print axioms guardCode_CupodV_DimcidV_eq_instB
#print axioms guardCode_DupocV_DimcidTV_eq_instB
#print axioms eval_qCD_iff_V
#print axioms eval_qCD_swapped_iff_V
#print axioms pDC_all_V
#print axioms pDC_guards_V
#print axioms eval_pDC_iff_std
#print axioms eval_pDC_iff_swap
#print axioms loebSound_pDC
#print axioms loeb_Dimcid_vs_Cupod_core_of_nec
#print axioms loeb_Dimcid_vs_Cupod_of_nec
#print axioms loeb_Dimcid_vs_Cupod_guards_of_nec
#print axioms loeb_Dimcid_vs_Cupod
#print axioms loeb_Dimcid_vs_Cupod_guards

-- Route B Phase 2, the JustBot family (Cells/JustBot, 2026-09-23) — the frozen-`.bot` Löb families. `pBot p` runs `p`
-- in the SAME frame (`EvalGraph.bot_iff`) and the canonical description commutes with it (`canonical_pBot`/`revalueU_pBot`/
-- `revalueW_pBot`), so Dupoc's search clause holds in ANY frame (`dupoc_frame_search_V`) and the bot-wrapped guards are
-- `k`-instances over the bot tower `TBD` (`termSubst_TBD`); the per-cell substitution computations are factored into
-- the generic instance equation `guardCode_eq_instB_of` and truth equation `eval_GtmplA_subst_iff`. Family (1)
-- `pBD = qBD ⋏ qBC`: **`loeb_botDupoc_vs_botDupoc`** — the engine's `loeb_botDupoc_vs_botDupoc_of_nec`, `EvalGraph 3 (pBot
-- (Dupoc k)) (pBot (Dupoc k)) (pBot (Dupoc k)) 0` for all large `k` (fuel 3: bot, search, const). `JustV k = pSearch k
-- (gJ k) (pConst 0) (pConst 1)` on the PRE-FILLED template `gJ k = subst (jVec k) ⌜guardTemplate 0⌝` (me-slots = the closed
-- description of `pBot (DupocV k)`, opp-slots = the frame variables): `guardCode_JustV` — Just's guard against `opp` IS
-- Dupoc-in-bot's guard against `opp`; at ℕ `Just k = pSearch k ⌜guardTemplateJust k⌝ …` with the bridge `JustV_nat`. Family (3)
-- `pJM = qJM ⋏ qJC` ("Mirror plays C against `pBot (Dupoc k)`"): **`loeb_Just_vs_Mirror`** — `EvalGraph 2
-- (Just k) Mirror (Just k) 0 ∧ EvalGraph 3 Mirror (Just k) Mirror 0`, the `(C, C)` cell (the engine's
-- `llm_outcome_JustBot_vs_MirrorBot`), plus the bot-wrapped Dupoc × Mirror and the box forms. Just × Just and
-- Just × Dupoc are NOT here: Just's own description carries the leaf `binNumeral (gJ k)`, so no fixed formula has those
-- guards as `k`-instances (see the module docstring).
#print axioms canonical_pBot
#print axioms dupoc_frame_search_V
#print axioms botDupoc_frame_search_V
#print axioms val_TBD_V
#print axioms termSubst_TBD
#print axioms guardCode_eq_instB_of
#print axioms eval_GtmplA_subst_iff
#print axioms guardCode_botDupocV_eq_instB
#print axioms guardCode_botCupodV_eq_instB
#print axioms eval_qBD_iff_V
#print axioms eval_qBC_iff_V
#print axioms pBD_both_V
#print axioms loebSound_pBD
#print axioms loeb_botDupoc_vs_botDupoc_core_of_nec
#print axioms loeb_botDupoc_vs_botDupoc_of_nec
#print axioms loeb_botDupoc_vs_botDupoc_guard_of_nec
#print axioms loeb_botDupoc_vs_botDupoc
#print axioms loeb_botCupod_vs_botCupod
#print axioms loeb_botDupoc_vs_botDupoc_guard
#print axioms termSubstVec_jVec
#print axioms guardCode_JustV
#print axioms just_search_V
#print axioms quote_guardTemplateJust
#print axioms JustV_nat
#print axioms guardCode_botDupocV_MirrorV_eq_instB
#print axioms guardCode_botCupodV_MirrorV_eq_instB
#print axioms eval_qJM_iff_V
#print axioms eval_qJC_iff_V
#print axioms pJM_both_V
#print axioms loebSound_pJM
#print axioms loeb_Just_vs_Mirror_core_of_nec
#print axioms loeb_Just_vs_Mirror_of_nec
#print axioms loeb_botDupoc_vs_Mirror_of_nec
#print axioms loeb_Just_vs_Mirror_guard_of_nec
#print axioms loeb_Just_vs_Mirror
#print axioms loeb_botDupoc_vs_Mirror
#print axioms loeb_Just_vs_Mirror_guard

-- Route (c) — templates with a BUDGET SLOT (ROUTE_B_SCOPE §8, 2026-09-23). The trusted base: `descriptionsB me opp k` =
-- `descriptions me opp` extended by `binNumeral k` in a SEVENTH slot `#6` (LAST, so every six-variable template and `descriptions`
-- are byte-identical), `guardCodeB g me opp k := subst (descriptionsB me opp k) g` (Σ₁), and the evaluator's search clause
-- (`EvalGraph`'s `Phi`/blueprint/`case_iff`, `EvalN.search_iff`) consults `LenBox TAct k (guardCodeB g me opp
-- k)`. THE GATE LEMMA `guardCodeB_of_template`: a six-variable template never reads the seventh entry (via the
-- identity vector `idVec6`: `subst_eq_self` at (6,6), `substs_substs` at (6,7)); `EvalGraph.search_iff₆` is the
-- pre-route-(c) reading on six-variable templates and repaired every use site; `substTemplate`/`substCode` unchanged.
-- Cells/JustSlot: Just's template becomes the CONSTANT `guardTemplateJust7 = (guardTemplate 0 ⇜ ![TBD(#0), cl uD, cl wD, #1, #2, #3])
-- ⇜ ![#6, #3, #4, #5]`; `JustV7 k = pSearch k ⌜guardTemplateJust7⌝ (pConst 0) (pConst 1)` is a `binNumeral k`-instance of a fixed
-- term (`TJ`, `canonical_JustV7`), `guardCodeB_guardTemplateJust7` (Just's guard against `opp` = the bot-wrapped Dupoc's guard
-- against `opp`), `evalGraph_JustV7_iff` (`JustV7 k` and `JustV k` play identically in every frame; the Mirror cell
-- transfers). The three parked cells, all unconditional: **`loeb_Just7_vs_Just7`** (Just × Just `(C, C)`,
-- family `pJJ = (qJJ ⋏ τqJJ) ⋏ pBD`, slack (14, 16)), **`loeb_Just7_vs_Dupoc`** (Just × Dupoc `(C, C)`,
-- the three-guard mutual family `pJD`, a THREE-level ∧-elimination at slack (21, 24)),
-- **`loeb_Cimcic_vs_Just7`** (CIMCIC × Just `(C, C)`, family `pCJ = pGC TJ uJ wJ ⋏ ((qJCi ⋏ τ) ⋏ pGC TBD uD
-- wD)`, slack (21, 24)), plus the box forms with the node-budget guard code of the constant template.
#print axioms guardCodeB_of_template
#print axioms guardCodeB_of_sentence
#print axioms guardCodeB_substTemplate
#print axioms EvalGraph.search_iff
#print axioms EvalGraph.search_iff₆
#print axioms quote_emb_castLE_V
#print axioms termSubst_tower_of
#print axioms termSubst_TBD_of
#print axioms termRelabelVec_descriptionsB
#print axioms revalueTemplate_guardCodeB
#print axioms revalueTemplate_quote_sentence₇_V
#print axioms lMap_swap_guardTemplateJust7
#print axioms quote_guardTemplateJust7A
#print axioms quote_qJ4
#print axioms termSubstVec_sVec7
#print axioms termSubstVec_jVec4
#print axioms guardCodeB_guardTemplateJust7A
#print axioms guardCodeB_guardTemplateJust7
#print axioms guardCodeB_guardTemplateJust7T
#print axioms transposeCode_JustV7
#print axioms just7_search_V
#print axioms just7T_search_V
#print axioms evalGraph_JustV7_iff
#print axioms evalGraph_Just7_iff

-- The `.sim` debt of route (c) DISCHARGED (2026-09-24): `substTemplate` gets a MIDDLE case — a seven-variable template
-- (not a six-variable one) is filled in `#0..#5` with the OUTER descriptions and KEEPS `#6` a variable
-- (`guardCodeSlot g me opp := subst (descriptionsSlot me opp) g`, `substTemplate_of_template₇`; `substTemplateGraph` gets the third
-- disjunct; `substTemplate_of_not` now needs `¬IsSemiformula LAct 7 g`). The node that runs the guard fills the slot with
-- ITS budget: `guardCodeB_substTemplate₇ : guardCodeB (substTemplate me opp g) me' opp' k = guardCodeB g me opp k` (via
-- `substs_substs` at (7, 7, 0) and `termSubstVec_descriptionsB_descriptionsSlot`), the seven-variable twin of
-- `guardCode_substTemplate`; τ-equivariance keeps its statement (`termRelabelVec_descriptionsSlot`: the swap fixes `^#6`).
-- Faithfulness witnesses: `sim_search_outer_guard₇` (any seven-variable searcher under `sim` reads the outer frame
-- at its own budget) and `Cells/SimSlot`'s `evalGraph_sim_JustV7` (`pSim (JustV7 k) q` runs Just's guard against
-- the OUTER `opp` — the engine's `.sim (JustBot k) q`).
#print axioms descriptionsSlot_semitermVec
#print axioms termSubstVec_descriptionsB_descriptionsSlot
#print axioms guardCodeB_guardCodeSlot
#print axioms isSemiformula_of_le
#print axioms substTemplate_of_template₇
#print axioms substTemplate_of_not
#print axioms isSemiformula_substTemplate₇
#print axioms guardCodeB_substTemplate₇
#print axioms termRelabelVec_descriptionsSlot
#print axioms revalueTemplate_substTemplate
#print axioms sim_search_outer_guard₇
#print axioms evalGraph_substCode_JustV7_iff
#print axioms evalGraph_sim_JustV7
#print axioms evalGraph_sim_JustV7_self
#print axioms loeb_Just7_vs_Mirror
#print axioms canonical_JustV7
#print axioms revalueU_JustV7
#print axioms revalueW_JustV7
#print axioms val_TJ_V
#print axioms revalue_val_uJ_wJ_V
#print axioms revalue_val_uJT_wJT_V
#print axioms hX_just7
#print axioms desc_just7
#print axioms descT_just7
#print axioms desc_botDupoc
#print axioms descT_botDupoc
#print axioms slack6_le
#print axioms slack6_le'
#print axioms slack6_le₁
#print axioms guardCode_botDupocV_JustV7_eq_instB
#print axioms guardCode_botCupodV_JustTV7_eq_instB
#print axioms eval_qJJ_iff_V
#print axioms eval_qJJ_swapped_iff_V
#print axioms pJJ_all_V
#print axioms pJJ_guards_V
#print axioms loebSound_pJJ
#print axioms loeb_Just7_vs_Just7_core_of_nec
#print axioms loeb_Just7_vs_Just7_of_nec
#print axioms loeb_Just7_vs_Just7
#print axioms loeb_Just7_vs_Just7_guard
#print axioms guardCode_botDupocV_DupocV_eq_instB
#print axioms guardCode_DupocV_botDupocV_eq_instB
#print axioms guardCode_DupocV_JustV7_eq_instB
#print axioms guardCode_CupodV_JustTV7_eq_instB
#print axioms eval_qJD_iff_V
#print axioms eval_qBDD_iff_V
#print axioms eval_qDJ_iff_V
#print axioms pJD_guards_V
#print axioms pJD_all_V
#print axioms loebSound_pJD
#print axioms loeb_Just7_vs_Dupoc_core_of_nec
#print axioms loeb_Just7_vs_Dupoc_of_nec
#print axioms loeb_Just7_vs_Dupoc
#print axioms loeb_Just7_vs_Dupoc_guards
#print axioms guardCode_botDupocV_CimcicV_eq_instB
#print axioms guardCode_botCupodV_CimcicTV_eq_instB
#print axioms eval_qJCi_iff_V
#print axioms pCJ_all_V
#print axioms loebSound_pCJ
#print axioms loeb_Cimcic_vs_Just7_core_of_nec
#print axioms loeb_Cimcic_vs_Just7_of_nec
#print axioms loeb_Cimcic_vs_Just7
#print axioms loeb_Cimcic_vs_Just7_guards

-- Route B Phase 2, the CIMCIC family — CIMCIC × Dupoc, CIMCIC × Mirror and CIMCIC × CIMCIC, all `(C, C)`, in
-- PA-`S'` (Cells/CIMCIC, 2026-09-23): `Cells/DIMCID` re-run on the guard `phiC = .impl (.plays .self .opp C)
-- (.plays .opp .self C)` with the branches exchanged (`CimcicV k = pSearch k ⌜templateC⌝ (pConst 0) (pConst 1)`,
-- `progCode (PD.Bots.CIMCIC k) = Cimcic k`; the transposed searcher `CimcicTV`, τ(CIMCIC), is not a zoo bot). The
-- fixed formulas generic in the opponent triple (`qCG`/`qCTG`, the family `pGC X U W`), the instance equations on
-- codes in every model, the search clauses (found ⇒ C / found ⇒ D), `pGC_both_V` the ∧-elimination.
-- Cell 1, the MUTUAL family CIMCIC × Dupoc `(C, C)` (engine `mutual_pblt_engine_id`): Dupoc's guard against CIMCIC
-- `qDCi = qG 0 TD uD wD TCi uCi wCi` ("CIMCIC plays C against me") on DIMCID's generic hand-written instance, the
-- four-guard family `pCiD = pGC TD uD wD ⋏ (qDCi ⋏ τqDCi)` with the two-level ∧-elimination at slack `(14, 16)`
-- (`pCiD_all_V`): CIMCIC cooperates with Dupoc, Dupoc cooperates with CIMCIC, so CIMCIC's implications have TRUE
-- consequents and Dupoc's atoms are TRUE in both readings (`loebSound_pCiD : LoebSound pCiD 14 16`); `family_found`
-- gives the cell, conditional on `BoundedInnerNec d`, then UNCONDITIONAL at `boundedInnerNec_sixteen`:
-- both cooperate at fuel 2, both find their guards. Cell 2, CIMCIC × Mirror `(C, C)`: Mirror COPIES at fuel 3.
-- Cell 3, CIMCIC × CIMCIC `(C, C)` with NO Löb: `qCC = qCG TCi uCi wCi` is `A → A` in both readings, so
-- `TAct ⊢ ∀¹ qCC` by completeness (`tact_proves_qCC`, the `S'` twin of `Pf.implRefl`), a proof code of standard
-- length in every model (`exists_qCC_length`), instantiated at `binNumeral k` (`qCC_inst_V`); at ℕ the instance costs
-- `K₀ + K₁·size k`, below `k` for all large `k` (`linear_size_le_eventually`) — `pos_Cimcic_vs_Cimcic_guard` and
-- `pos_Cimcic_vs_Cimcic` need no `BoundedInnerNec` at all. Nothing in `Code`/`Agent`/`Det`/`Instance*` was changed.
#print axioms progCode_CIMCIC
#print axioms transposeCode_CimcicV
#print axioms canonical_CimcicV
#print axioms eval_templateC_V
#print axioms eval_templateCT_V
#print axioms eval_qCG_iff_V
#print axioms eval_qCTG_iff_V
#print axioms guardCode_CimcicV_eq_instB
#print axioms guardCode_CimcicTV_eq_instB
#print axioms cimcic_search_V
#print axioms cimcicT_search_V
#print axioms pGC_both_V
#print axioms pGC_guards_V
#print axioms eval_pGC_iff_std
#print axioms eval_pGC_iff_swap
#print axioms guardCode_CimcicV_DupocV_eq_instB
#print axioms guardCode_DupocV_CimcicV_eq_instB
#print axioms guardCode_CupodV_CimcicTV_eq_instB
#print axioms eval_qCDu_iff_V
#print axioms eval_qCDu_swap_iff_V
#print axioms eval_qDCi_iff_V
#print axioms eval_qDCi_swapped_iff_V
#print axioms pCiD_all_V
#print axioms pCiD_guards_V
#print axioms eval_pCiD_iff_std
#print axioms eval_pCiD_iff_swap
#print axioms loebSound_pCiD
#print axioms loeb_Cimcic_vs_Dupoc_core_of_nec
#print axioms loeb_Cimcic_vs_Dupoc_of_nec
#print axioms loeb_Cimcic_vs_Dupoc_guards_of_nec
#print axioms loeb_Cimcic_vs_Dupoc
#print axioms loeb_Cimcic_vs_Dupoc_guards
#print axioms guardCode_CimcicV_MirrorV_eq_instB
#print axioms eval_qCMi_iff_V
#print axioms eval_qCMi_swap_iff_V
#print axioms loebSound_pCMi
#print axioms loeb_Cimcic_vs_Mirror_core_of_nec
#print axioms loeb_Cimcic_vs_Mirror_of_nec
#print axioms loeb_Cimcic_vs_Mirror_guard_of_nec
#print axioms loeb_Cimcic_vs_Mirror
#print axioms loeb_Cimcic_vs_Mirror_guard
#print axioms guardCode_CimcicV_self_eq_instB
#print axioms eval_qCC_iff_V
#print axioms eval_qCC_swap_iff_V
#print axioms tact_proves_qCC
#print axioms exists_qCC_length
#print axioms qCC_inst_V
#print axioms linear_size_le_eventually
#print axioms pos_Cimcic_vs_Cimcic_guard
#print axioms pos_Cimcic_vs_Cimcic
#print axioms pos_CIMCIC_vs_CIMCIC_guardOf

-- Route B Phase 2, the PrudentBot family (Cells/PrudentMirror, 2026-09-23) — the NESTED-search Löb family. STEP 0:
-- `PrudentBot k`'s two stored templates are budget-free constants (`templateP1`/`templateP2`; `.bot DefectBot` is closed), so
-- `PrudentV k` is a `binNumeral k`-instance of a fixed two-`#0` term (`TP`, `termSubst_tower'`/`termSubst_TP`) — NOT the JustBot
-- obstruction; the bridge is `progCode_PrudentBot`. The cost of the nesting: the canonical description compares two
-- `k`-dependent codes, so `canonical/revalueU/revalueW` are `k`-uniform only above the standard threshold `KP` (`nested_search_lt`, an
-- ordered-semiring argument on `ppair`; `canonical_PrudentV`), and the family's slack `S₀ = 14 + KP` supplies it inside the
-- Löb premise. Generic template instances for an ARBITRARY six-variable template (`guardCode_qT_eq_instB`, its swap,
-- `eval_qT_iff`) and the atom over a closed program (`eval_template_plays_opp_closed_V`). The family `pPM = (qPM ⋏ qPP) ⋏
-- (qPMT ⋏ qPPT)` carries the PRUDENCE guard as a conjunct: the engine's inner-search citation (`searchThenSearch_t` +
-- `prudence_provable`) becomes an ∧-elimination from the same box (`pPM_all_V`), prudence itself being a closed true
-- Σ₁ fact in every model (`mirror_bot_defect_V`). `loebSound_pPM : LoebSound pPM (14 + KP) 16`, then the cells:
-- **`loeb_Prudent_vs_Mirror`** — `EvalGraph 3 (Prudent k) Mirror (Prudent k) 0 ∧ EvalGraph 4 Mirror (Prudent k)
-- Mirror 0` for all large `k`, the `(C, C)` cell (engine `outcome_PrudentBot_vs_MirrorBot`) — and the transposed
-- searcher's `(D, D)` twin, plus the box forms (Prudent FINDS both its guards within `k`).
#print axioms progCode_PrudentBot
#print axioms transposeCode_PrudentV
#print axioms nested_search_lt
#print axioms innerP2_ne_innerT2
#print axioms PrudentV_lt_PrudentTV
#print axioms canonical_PrudentV
#print axioms revalueU_PrudentV
#print axioms revalueW_PrudentV
#print axioms revalue_val_uP_wP_V
#print axioms revalue_val_uPT_wPT_V
#print axioms termSubst_tower'
#print axioms val_TP_V
#print axioms termSubst_TP
#print axioms guardCode_qT_eq_instB
#print axioms guardCode_qT_swap_eq_instB
#print axioms eval_qT_iff
#print axioms eval_template_plays_opp_closed_V
#print axioms guardCode_PrudentV_MirrorV_eq_instB
#print axioms guardCode_PrudentV_MirrorV_inner_eq_instB
#print axioms guardCode_PrudentTV_MirrorV_eq_instB
#print axioms guardCode_PrudentTV_MirrorV_inner_eq_instB
#print axioms eval_qPM_iff_V
#print axioms eval_qPP_iff_V
#print axioms eval_qPMT_iff_V
#print axioms eval_qPPT_iff_V
#print axioms mirror_bot_defect_V
#print axioms mirror_bot_coop_V
#print axioms prudent_search_V
#print axioms prudentT_search_V
#print axioms pPM_all_V
#print axioms pPM_guards_V
#print axioms eval_pPM_iff_std
#print axioms eval_pPM_iff_swap
#print axioms loebSound_pPM
#print axioms loeb_Prudent_vs_Mirror_core_of_nec
#print axioms loeb_Prudent_vs_Mirror_of_nec
#print axioms loeb_PrudentT_vs_Mirror_of_nec
#print axioms loeb_Prudent_vs_Mirror_guards_of_nec
#print axioms loeb_Prudent_vs_Mirror
#print axioms loeb_PrudentT_vs_Mirror
#print axioms loeb_Prudent_vs_Mirror_guards

-- Route B Phase 4, the SEARCH-FREE class (Cells/SearchFree, 2026-09-23) — the 28 SF cells of `ROUTE_B_CENSUS.md`
-- (both players in {CooperateBot, DefectBot, MirrorBot, TitForTatBot, DBot, EBot, OBot}: `const/sim/ite` only) in
-- PA-`S'` at ℕ, UNCONDITIONAL (no oracle, no Löb, no floor, no budget: the evaluator never consults `□_k`). The
-- engine's `OutcomeSpec .nobudget pad` theorems are TRANSFERRED at the SAME fuel: `evalGraph_of_eval_searchFree`
-- (the `Inv true` clause-by-clause induction of `AgentConverse.evalGraph_of_eval_core`, fuels coinciding, the
-- `.search` arm vacuous), the bridge `outcome_evalGraph_of_searchFree` / `outcomeSpec_evalGraph_of_searchFree`
-- (an engine outcome at fuel `n` on search-free proper modest players = the pair of arithmetized plays at fuel
-- `n`), the seven players as `SearchFreePlayer`, the 27 terminating cells `sf_<L>_vs_<R> : EvalGraph pad ⌜L⌝ ⌜R⌝
-- ⌜L⌝ a ∧ EvalGraph pad ⌜R⌝ ⌜L⌝ ⌜R⌝ b` at the engine's pads (1–11), the `none` cell `sf_MirrorBot_vs_MirrorBot`
-- as NON-termination at every fuel (`SimTest.mirror_vs_mirror`), PA proving every positive atom
-- (`pa_proves_sentenceAt_of_evalGraph`: an arithmetized play at ℕ ⇒ the instantiated atom sentence is a PA theorem by
-- Σ₁-completeness, no engine certificate; `pa_<L>_vs_<R> : 𝗣𝗔 ⊢ Aι L R a ∧ 𝗣𝗔 ⊢ Aι R L b`), and the census in one
-- line each: `searchFree_census` (28 cells), `searchFree_pa_census` (54 atoms).
#print axioms evalGraph_of_eval_searchFree_core
#print axioms evalGraph_of_eval_searchFree
#print axioms play_evalGraph_of_searchFree
#print axioms outcome_evalGraph_of_searchFree
#print axioms outcomeSpec_evalGraph_of_searchFree
#print axioms pa_proves_sentenceAt_of_evalGraph
#print axioms pa_cell_of_evalGraph
#print axioms progCode_MirrorBot
#print axioms sf_CooperateBot_vs_CooperateBot
#print axioms sf_CooperateBot_vs_DefectBot
#print axioms sf_DBot_vs_CooperateBot
#print axioms sf_DBot_vs_DBot
#print axioms sf_DBot_vs_DefectBot
#print axioms sf_DefectBot_vs_DefectBot
#print axioms sf_EBot_vs_CooperateBot
#print axioms sf_EBot_vs_DBot
#print axioms sf_EBot_vs_DefectBot
#print axioms sf_EBot_vs_EBot
#print axioms sf_EBot_vs_MirrorBot
#print axioms sf_EBot_vs_OBot
#print axioms sf_EBot_vs_TitForTatBot
#print axioms sf_MirrorBot_vs_CooperateBot
#print axioms sf_MirrorBot_vs_DBot
#print axioms sf_MirrorBot_vs_DefectBot
#print axioms sf_MirrorBot_vs_MirrorBot
#print axioms sf_MirrorBot_vs_OBot
#print axioms sf_MirrorBot_vs_TitForTatBot
#print axioms sf_OBot_vs_CooperateBot
#print axioms sf_OBot_vs_DBot
#print axioms sf_OBot_vs_DefectBot
#print axioms sf_OBot_vs_OBot
#print axioms sf_OBot_vs_TitForTatBot
#print axioms sf_TitForTatBot_vs_CooperateBot
#print axioms sf_TitForTatBot_vs_DBot
#print axioms sf_TitForTatBot_vs_DefectBot
#print axioms sf_TitForTatBot_vs_TitForTatBot
#print axioms pa_CooperateBot_vs_CooperateBot
#print axioms pa_CooperateBot_vs_DefectBot
#print axioms pa_DBot_vs_CooperateBot
#print axioms pa_DBot_vs_DBot
#print axioms pa_DBot_vs_DefectBot
#print axioms pa_DefectBot_vs_DefectBot
#print axioms pa_EBot_vs_CooperateBot
#print axioms pa_EBot_vs_DBot
#print axioms pa_EBot_vs_DefectBot
#print axioms pa_EBot_vs_EBot
#print axioms pa_EBot_vs_MirrorBot
#print axioms pa_EBot_vs_OBot
#print axioms pa_EBot_vs_TitForTatBot
#print axioms pa_MirrorBot_vs_CooperateBot
#print axioms pa_MirrorBot_vs_DBot
#print axioms pa_MirrorBot_vs_DefectBot
#print axioms pa_MirrorBot_vs_OBot
#print axioms pa_MirrorBot_vs_TitForTatBot
#print axioms pa_OBot_vs_CooperateBot
#print axioms pa_OBot_vs_DBot
#print axioms pa_OBot_vs_DefectBot
#print axioms pa_OBot_vs_OBot
#print axioms pa_OBot_vs_TitForTatBot
#print axioms pa_TitForTatBot_vs_CooperateBot
#print axioms pa_TitForTatBot_vs_DBot
#print axioms pa_TitForTatBot_vs_DefectBot
#print axioms pa_TitForTatBot_vs_TitForTatBot
#print axioms searchFree_census
#print axioms searchFree_pa_census

-- Route B Phase 4, the SND class (Cells/SoundnessCells, 2026-09-23) — the cells of `ROUTE_B_CENSUS.md` whose searcher
-- takes its ELSE branch because its guard is semantically FALSE, in PA-`S'` at ℕ, unconditional (no oracle, no Löb,
-- no floor): `TAct` is sound in ℕ, so a false guard has no proof of ANY length (`snd_else_of_false`, the red cell's
-- argument), the search clause takes the else branch, and the partner's play follows from its own clauses. The
-- guard's realization in a proper frame is the realization of its closed instantiation (`sentenceAt_subst`), the truth
-- equations of the four guard shapes (`models_sentenceAt_plays`, `models_sentenceAt_neg`, `models_sentenceAt_eq`, `models_sentenceAt_impl`)
-- give the "not found" lemmas per shape (`not_found_opp_self`/`_opp_bot`/`_neg_opp_self`/`_eq_opp`), the
-- search clause on engine templates (`search_else`/`search_then`/`search_either` — a node whose branches agree needs
-- no verdict: Prudent's outer guard, Dupoc's/Just's probe against `.bot CooperateBot` inside OBot), and the
-- search-free probers' plays from their probe results (`dbot_*`, `tft_*`, `obot_*`, `ebot_*`, `mirror_copies`).
-- Template disjointness for CupodTroll's `.eq` guard is SEMANTIC (`templateCode_ne_of_models`: two guards whose realizations
-- differ in truth at one frame have different codes — Wary vs Cupod separated at the non-terminating frame
-- `(Mirror, Mirror)`). The 30 cells `snd_<L>_vs_<R>` at the engine's pads: Guardian 6, CupodTroll 8, Prudent 6,
-- Wary 4, Cupod 2, Dupoc 2, Just 2 (on the engine's own code `progCode (JustBot k)`). Also the positive kit for
-- CLOSED atoms: `tact_proves_plays_closed` (Σ₁-completeness of PA at ℕ in both readings, `lMap_swap_sentenceAt`, then
-- `TAct_complete_of_readings`) and `found_of_tact`.
#print axioms snd_else_of_false
#print axioms sentenceAt_subst
#print axioms sentenceAt_neg
#print axioms sentenceAt_impl
#print axioms models_sentenceAt_neg
#print axioms models_sentenceAt_impl
#print axioms models_sentenceAt_eq
#print axioms not_found_opp_self
#print axioms not_found_opp_bot
#print axioms not_found_neg_opp_self
#print axioms not_found_eq_opp
#print axioms found_of_tact
#print axioms tact_proves_plays_closed
#print axioms search_else
#print axioms search_then
#print axioms search_either
#print axioms templateCode_ne_of_models
#print axioms templateCode_phiG_ne_phiCu
#print axioms templateCode_phiT_ne_phiCu
#print axioms templateCode_phiW_ne_phiCu
#print axioms snd_GuardianBot_vs_CupodBot
#print axioms snd_GuardianBot_vs_CupodTrollBot
#print axioms snd_GuardianBot_vs_GuardianBot
#print axioms snd_GuardianBot_vs_TitForTatBot
#print axioms snd_GuardianBot_vs_CooperateBot
#print axioms snd_GuardianBot_vs_MirrorBot
#print axioms snd_CupodTrollBot_vs_CooperateBot
#print axioms snd_CupodTrollBot_vs_CupodTrollBot
#print axioms snd_CupodTrollBot_vs_DBot
#print axioms snd_CupodTrollBot_vs_DefectBot
#print axioms snd_CupodTrollBot_vs_EBot
#print axioms snd_CupodTrollBot_vs_MirrorBot
#print axioms snd_CupodTrollBot_vs_OBot
#print axioms snd_CupodTrollBot_vs_TitForTatBot
#print axioms snd_PrudentBot_vs_CooperateBot
#print axioms snd_PrudentBot_vs_CupodTrollBot
#print axioms snd_PrudentBot_vs_DBot
#print axioms snd_PrudentBot_vs_DefectBot
#print axioms snd_PrudentBot_vs_OBot
#print axioms snd_PrudentBot_vs_TitForTatBot
#print axioms snd_WaryBot_vs_CooperateBot
#print axioms snd_WaryBot_vs_CupodTrollBot
#print axioms snd_WaryBot_vs_GuardianBot
#print axioms snd_WaryBot_vs_TitForTatBot
#print axioms snd_CupodBot_vs_CooperateBot
#print axioms snd_CupodBot_vs_TitForTatBot
#print axioms snd_DupocBot_vs_DefectBot
#print axioms snd_DupocBot_vs_OBot
#print axioms snd_JustBot_vs_DefectBot
#print axioms snd_JustBot_vs_OBot

-- (batch 2) Guardian's guard names no `.self`, so against a closed opponent `X` its realization is the FIXED closed
-- atom "`X` defects against `.bot CooperateBot`" (`sentenceAt_subst`); `TAct` proves such an atom by Σ₁-completeness of PA
-- at ℕ in BOTH readings (the transposed play by the engine's `decide` through the search-free lockstep transfer,
-- `evalGraph_transpose_of_eval`; `lMap_swap_template_plays` needs no atomicity) and completeness (`TAct_complete_of_readings`), and
-- the guard is found above that proof's length (`guardian_found`). The four cells: `pos_GuardianBot_vs_DefectBot`
-- `(D, D)`, `pos_GuardianBot_vs_DBot` `(D, C)`, and the two SND cells with a positive sub-fact,
-- `pos_GuardianBot_vs_EBot` `(D, C)` and `pos_GuardianBot_vs_OBot` `(C, D)`, all for large `k` at the engine's pads.
#print axioms lMap_swap_template_plays
#print axioms lMap_swap_sentenceAt_plays
#print axioms sfp_transpose
#print axioms guardian_found
#print axioms evalGraph_transpose_of_eval
#print axioms tact_DB_D_vs_botCB
#print axioms tact_botDB_D_vs_botCB
#print axioms tact_DBot_D_vs_botCB
#print axioms tact_EBot_D_vs_botCB
#print axioms pos_GuardianBot_vs_botDB
#print axioms pos_GuardianBot_vs_DefectBot
#print axioms pos_GuardianBot_vs_DBot
#print axioms pos_GuardianBot_vs_EBot
#print axioms pos_GuardianBot_vs_OBot

-- Route B Phase 4, the POS class (Cells/PositiveCells, 2026-09-23) — cells whose searcher FINDS its guard without Löb,
-- in PA-`S'` at ℕ for all large `k`, unconditional (no `BoundedInnerNec`): the `S'` twin of the engine's `search_t` on
-- a search-free atom / `weakenImpl` / `atomNeg`. The mechanism (`pos_Cimcic_vs_Cimcic`'s, generic): the guard against a
-- CONSTANT opponent (`pConst 0`, `pConst 1`, `pBot (pConst 0)`, `pBot (pConst 1)` — their canonical triples in §1) is
-- the `binNumeral k`-instance of a FIXED one-variable formula `q` (`guardCode_qT_eq_instB` with the searcher's own
-- description triple), `q(k)` is true in BOTH standard readings of every model (the play of a constant is a fixed
-- clause: `const_play_V`/`bot_const_play_V`, and its negation by determinism for Wary's `.neg` guard:
-- `const_not_play_V`), so `TAct ⊢ ∀¹ q` by completeness (`tact_all_of_both`), and the instance at `binNumeral k` costs
-- `K₀ + K₁·size k ≤ k` for all large `k` (`found_of_all`). The GENERIC engine-searcher description layer
-- (`SV g a k := pSearch k ⌜g⌝ (pConst a) (pConst (1 - a))`, `transposeCode_SV`, `canonical_SV`/`revalueU_SV`/`revalueW_SV`, the tower
-- `TS`, `hX_SV`, `revalue_val_uS_wS_V`/`_uST_wST_V`) puts Dupoc's, Cupod's and Wary's ENGINE codes (`progCode (DupocBot k)`
-- etc., not the `guardTemplate` twins) on the same footing as CIMCIC/DIMCID, and the bot tower `TBS` describes the frozen
-- snapshot `pBot (progCode (DupocBot k))` of JustBot's guard (`guardCode_JustBot_eq`: Just's consulted guard IS Dupoc's
-- engine guard in the snapshot's frame). The cells: `pos_DupocBot_vs_CooperateBot` `(C, C)`,
-- `pos_CupodBot_vs_DefectBot` `(D, D)`, `pos_CIMCIC_vs_CooperateBot` `(C, C)`, `pos_DIMCID_vs_DefectBot` `(D, D)`,
-- `pos_JustBot_vs_CooperateBot` `(C, C)` (on the engine's own code), `pos_WaryBot_vs_DefectBot` `(D, D)` (the `.neg`
-- guard: a Π₁ truth by determinism), and the SND cells with a positive sub-fact `pos_CupodBot_vs_DBot`/`_EBot` `(C, C)`
-- (Cupod finds "`.bot DefectBot` defects against me") and `pos_WaryBot_vs_DBot`/`_EBot` `(C, C)`.
#print axioms canonical_pConst_zero
#print axioms canonical_pConst_one
#print axioms hX_const_zero
#print axioms hX_const_one
#print axioms hX_bot_zero
#print axioms hX_bot_one
#print axioms val_desc_const_zero
#print axioms val_desc_const_one
#print axioms transposeCode_SV
#print axioms canonical_SV
#print axioms revalueU_SV
#print axioms revalueW_SV
#print axioms val_TS_V
#print axioms hX_SV
#print axioms revalue_val_uS_wS_V
#print axioms revalue_val_uST_wST_V
#print axioms tact_all_of_both
#print axioms found_of_all
#print axioms eval_qT_plays_opp_self
#print axioms eval_qT_neg_plays_opp_self
#print axioms eval_qT_swap
#print axioms desc_SV
#print axioms descT_SV
#print axioms termSubst_TBS
#print axioms desc_botSV
#print axioms descT_botSV
#print axioms guardCode_JustBot_eq
#print axioms guardCode_Du0
#print axioms tact_qDu0
#print axioms pos_DupocBot_vs_CooperateBot
#print axioms guardCode_Cu1
#print axioms tact_qCu1
#print axioms pos_CupodBot_vs_DefectBot
#print axioms guardCode_CuB1
#print axioms tact_qCuB1
#print axioms pos_CupodBot_vs_botDB
#print axioms pos_CupodBot_vs_DBot
#print axioms pos_CupodBot_vs_EBot
#print axioms guardCode_Ci0
#print axioms tact_qCi0
#print axioms pos_CIMCIC_vs_CooperateBot
#print axioms guardCode_Di1
#print axioms tact_qDi1
#print axioms pos_DIMCID_vs_DefectBot
#print axioms guardCode_J0
#print axioms tact_qJ0
#print axioms pos_JustBot_vs_CooperateBot
#print axioms guardCode_W1
#print axioms tact_qW1
#print axioms pos_WaryBot_vs_DefectBot
#print axioms guardCode_WB1
#print axioms tact_qWB1
#print axioms pos_WaryBot_vs_botDB
#print axioms pos_WaryBot_vs_DBot
#print axioms pos_WaryBot_vs_EBot

-- (the unreadability cells re-evaluated) CIMCIC's guard against an opponent that defects against it is
-- SELF-REFUTING (`cimcic_selfref_not_found`): `snd_CIMCIC_vs_DefectBot` `(D, D)` at every `k`, `snd_CIMCIC_vs_OBot`
-- `(D, D)` for large `k` — the engine's values, by soundness instead of the unreadability census. And the FIRST
-- FLIPPED cell: `loeb_DIMCID_vs_CooperateBot` — DIMCID × CooperateBot is `(D, C)` in `S'` (engine: `(C, C)`), the
-- self-fulfilling refutation "I do not cooperate" found by bounded Löb (`loebSound_pDi0`, `family_found`).
#print axioms cimcic_selfref_not_found
#print axioms snd_CIMCIC_vs_DefectBot
#print axioms snd_CIMCIC_vs_botDB
#print axioms guardCode_CiB0
#print axioms tact_qCiB0
#print axioms pos_CIMCIC_vs_botCB
#print axioms snd_CIMCIC_vs_OBot
#print axioms loebSound_pDi0
#print axioms loeb_DIMCID_vs_CooperateBot

-- Route B, the FLIP cells (Cells/FlipCells, 2026-09-24) — where PA-`S'` DISAGREES with the engine's `S`: the
-- unreadability censuses do not transfer, and a NEGATIVE-Löb guard is self-fulfilling under a real proof
-- predicate. The generic Löb premise `loebSound_pG_of` (DIMCID's family against ANY described opponent — the
-- consequent is irrelevant) and `dimcid_vs_described`; the closed opponents `.bot CooperateBot` and TFT.
-- Cell 1: `loeb_DIMCID_vs_TitForTatBot` — DIMCID × TitForTatBot is `(D, D)` in `S'` (engine
-- `llm_outcome_DIMCID_vs_TitForTatBot = (C, C)`): the self-fulfilling refutation found by Löb, TFT's probe
-- sees DIMCID defect against `.bot CooperateBot`.
#print axioms loebSound_pG_of
#print axioms dimcid_vs_described
#print axioms describes_botCB
#print axioms TFTV_lt_TFTTV
#print axioms describes_TFT
#print axioms loeb_DIMCID_vs_botCB
#print axioms loeb_DIMCID_vs_TitForTatBot_core
#print axioms loeb_DIMCID_vs_TitForTatBot
#print axioms loeb_DIMCID_vs_TitForTatBot_guard

-- Cell 2: the box-consequence lemma (`BoxConseq`, `box_conseq_uniform`, `found_of_box_conseq` — the general
-- `k̂`-chain: a guard whose truth needs ANOTHER searcher's Löb-found guard is `TAct`-provable within the budget,
-- the chain instantiated at `binNumeral k`, the numeral and box antecedents cut away, the total polylog
-- `total_le_eventually`), `describes_SV` (the engine searchers' canonical triples), and
-- `loeb_GuardianBot_vs_DIMCID` — GuardianBot × DIMCID is `(D, D)` in `S'` (engine
-- `llm_outcome_GuardianBot_vs_DIMCID = (C, C)`): Guardian finds "DIMCID defects against `.bot CooperateBot`"
-- (`guardian_finds_DIMCID`), DIMCID's guard against Guardian is self-fulfilling.
#print axioms box_conseq_uniform
#print axioms total_le_eventually
#print axioms found_of_box_conseq
#print axioms describes_SV
#print axioms boxConseq_qGD
#print axioms guardian_finds_DIMCID
#print axioms loeb_DIMCID_vs_GuardianBot_core
#print axioms loeb_GuardianBot_vs_DIMCID
#print axioms loeb_DIMCID_vs_GuardianBot_guard

-- Cells 3, 4: the `.neg` family `pQ q := q ⋏ τq` (`pQ_both_V`, ∧-elimination on codes, slack `(7, 8)`), the search
-- clause of the generic engine searcher in every model (`SV_search_V`), and `loeb_WaryBot_vs_MirrorBot` /
-- `loeb_WaryBot_vs_WaryBot` — WaryBot × MirrorBot and WaryBot × WaryBot are `(D, D)` in `S'` (engine
-- `outcome_WaryBot_vs_MirrorBot`/`outcome_WaryBot_vs_WaryBot = (C, C)` at every `k`, `.neg`-guard valuation
-- censuses): "¬(you cooperate with me)" against a copier is SELF-FULFILLING — found ⇒ Wary defects ⇒ the copier
-- defects (`loebSound_pWM`, `loebSound_pWW`), bounded Löb finds it.
#print axioms pQ_both_V
#print axioms SV_search_V
#print axioms loebSound_pWM
#print axioms loebSound_pWW
#print axioms loeb_WaryBot_vs_MirrorBot_core
#print axioms loeb_WaryBot_vs_MirrorBot
#print axioms loeb_WaryBot_vs_MirrorBot_guard
#print axioms loeb_WaryBot_vs_WaryBot_core
#print axioms loeb_WaryBot_vs_WaryBot
#print axioms loeb_WaryBot_vs_WaryBot_guard

-- Route B, the `k̂`-CHAIN cells (Cells/KhatCells, 2026-09-24) — the four POS cells `Cells/PositiveCells.lean`
-- skipped: the searcher's guard is true only ABOVE a standard threshold `k̂`, because the opponent's play in a
-- model needs a guard FOUND in that model. `found_of_all_V` (a `TAct`-theorem `∀¹ q` is found at every large
-- budget in EVERY model — the instance costs `N + 5|q|·|binNumeral k| + 3|q| + |binNumeral k| + 7 ≤ C·‖k‖ ≤ k`),
-- `tact_all_above_of_both` (the conditional universal `∀¹ (k̂ ≤ #0 🡒 q)` by completeness), and
-- `found_of_all_above` (`found_of_all` with the numeral antecedent cut by `NumeralFacts.lenBoxNat_le_binNumeralMeta`,
-- cost `K₀ + K₁·size k + K₂·size k²`, below `k` for large `k`). TitForTatBot in every model (`TftV`, canonical:
-- `TftV_lt_TftTV`; the closed term `TTft`; `tft_C_of_probe_C_V`), the probes found above `k̂` in every model.
#print axioms found_of_all_V
#print axioms tact_all_above_of_both
#print axioms exists_instance_length_above
#print axioms found_of_all_above
#print axioms TftV_lt_TftTV
#print axioms val_desc_tft
#print axioms tft_C_of_probe_C_V
#print axioms SV_then_V
#print axioms dupoc_botCB_V
#print axioms cupod_botDB_V
#print axioms botDupoc_botCB_V
#print axioms botCupod_botDB_V
#print axioms cimcic_botCB_V
#print axioms cimcicT_botDB_V

-- The three TFT cells, unconditional at the engine's pads, on the engine's own codes: `khat_DupocBot_vs_TitForTatBot`
-- `(C, C)` (pad 4), `khat_JustBot_vs_TitForTatBot` `(C, C)` (pad 5, on `progCode (JustBot k)`: the consulted guard is
-- the frozen snapshot's, TFT sees `.bot (DupocBot k)` cooperate with `.bot CooperateBot`), and
-- `khat_CIMCIC_vs_TitForTatBot` `(C, C)` (pad 6, the engine's `weakenImpl`): TFT probes the searcher against
-- `.bot CooperateBot`, the searcher's guard "TFT cooperates with me" is true above `k̂`, found by the chain.
#print axioms guardCode_DT
#print axioms tact_qDT_above
#print axioms khat_DupocBot_vs_TitForTatBot
#print axioms pos_JustBot_vs_botCB
#print axioms guardCode_JT
#print axioms tact_qJT_above
#print axioms khat_JustBot_vs_TitForTatBot
#print axioms guardCode_CT
#print axioms tact_qCT_above
#print axioms khat_CIMCIC_vs_TitForTatBot

-- `CupodTroll7`: CupodTroll on a CONSTANT seven-variable template with the budget slot (route (c), the §7 shape:
-- `CupodTrollBot k` freezes the budget-carrying snapshot `CupodBot k` inside its `.eq` guard). The six-variable
-- base `eqTmpl` ("the opp-triple describes the me-triple's program", `eval_eqTmpl_V`), the template `guardTemplateTroll7`
-- reading Cupod's budget from `#6` through `TS gCu 1`, the instance equation `guardCodeB_guardTemplateTroll7`, the ENGINE
-- BRIDGE `guardCodeB_guardTemplateTroll7_nat` (the SAME code as the engine's `.eq .opp (CupodBot k)` guard, via the typed
-- equality `eqTmpl_subst_eq_template_eq`), hence `evalGraph_CupodTroll7_iff` (the same play as `progCode (CupodTrollBot k)`
-- in every frame at every fuel), and the description layer `TT/uT/wT`.
#print axioms eval_eqTmpl_V
#print axioms lMap_swap_eqTmpl
#print axioms eqTmpl_subst_eq_template_eq
#print axioms quote_subst_descriptionTerms
#print axioms guardCode_eqTmpl_eq_templateCode
#print axioms guardCodeB_guardTemplateTroll7A
#print axioms guardCodeB_guardTemplateTroll7
#print axioms guardCodeB_guardTemplateTroll7T
#print axioms guardCodeB_guardTemplateTroll7_nat
#print axioms transposeCode_CupodTrollV7
#print axioms troll7_then_V
#print axioms evalGraph_CupodTroll7_iff
#print axioms canonical_CupodTrollV7
#print axioms hX_troll7
#print axioms desc_troll7
#print axioms descT_troll7

-- CupodTroll × Cupod `(D, D)` (engine `outcome_CupodTrollBot_vs_CupodBot`, pad 2): CupodTroll's `.eq` guard
-- against `CupodBot k` is the reflexive equation `qEqSelf` (`tact_qEqSelf`, both readings), found by `found_of_all`
-- ⇒ then-branch D (`khat_CupodTrollBot_vs_CupodBot_guard`, the box form on the engine's codes); Cupod's guard "CupodTroll
-- defects against me" is then TRUE above `k̂` in every model (`troll7_vs_cupod_D_V`) and found by the chain ⇒ D:
-- `khat_CupodTrollBot_vs_CupodBot` (on `CupodTroll7 k`, the described code) and `_engine` (CupodTroll's half on
-- `progCode (CupodTrollBot k)`).
#print axioms tact_qEqSelf
#print axioms troll7_vs_cupod_D_V
#print axioms troll7T_vs_dupoc_C_V
#print axioms guardCode_CuT7
#print axioms tact_qCuT7_above
#print axioms khat_CupodTrollBot_vs_CupodBot_guard
#print axioms khat_CupodTrollBot_vs_CupodBot
#print axioms khat_CupodTrollBot_vs_CupodBot_engine

-- Cell 5: `loeb_DIMCID_vs_CupodTrollBot` — DIMCID × CupodTrollBot is `(D, C)` in `S'` (engine
-- `llm_outcome_DIMCID_vs_CupodTrollBot = (C, C)`), on the budget-slot `CupodTroll7 k` of `Cells/KhatCells`
-- (the same play as the engine's `CupodTrollBot k` in every frame): DIMCID's guard against the described
-- CupodTroll (`describes_troll7`) is self-fulfilling; CupodTroll's `.eq` guard "DIMCID is `CupodBot k`" is FALSE
-- (`templateCode_phiD_ne_phiCu`, `progCode_DIMCID_ne_CupodBot`), never found by soundness, so CupodTroll cooperates
-- (`snd_CupodTroll7_vs_DIMCID`, and on the engine's own code `snd_CupodTrollBot_vs_DIMCID_engine`, at every `k`).
#print axioms templateCode_phiD_ne_phiCu
#print axioms progCode_DIMCID_ne_CupodBot
#print axioms snd_CupodTroll7_vs_DIMCID
#print axioms snd_CupodTrollBot_vs_DIMCID_engine
#print axioms describes_troll7
#print axioms loeb_DIMCID_vs_CupodTroll7
#print axioms loeb_DIMCID_vs_CupodTrollBot
#print axioms loeb_DIMCID_vs_CupodTroll7_guard

-- Route B, DIMCID's ROW (Cells/DimcidFlips, 2026-09-24) — the seven cells where the engine has DIMCID COOPERATING,
-- every one by a census (a floor `no_provable_tailToS_floor`, a probe-first floor, or an unreadability census)
-- that cannot read DIMCID's own guard; `dimcid_vs_described` (FlipCells) says DIMCID defects against every
-- described opponent in `S'`. (1) EVERY CLOSED CODE IS DESCRIBED (`describes_closed`: the generic triple
-- `(cl (canonicalMeta P), revalueUMeta P, revalueWMeta P)` of Template.lean, in every model, via the absoluteness of `transposeCode`/`canonical`)
-- ⇒ `dimcid_vs_closed`: DIMCID defects against every closed code (DBot, EBot, OBot, the frozen `.bot` probes).
-- (2) A description ABOVE a threshold (`DescribesAbove K`, Prudent's `KP`; `loebSound_pG_of_above` with slack
-- `(7 + K, 8)`, `dimcid_vs_described_above`). (3) The instances: `describes_botSV` (the bot-wrapped engine
-- searcher `pBot (SV g a k)`), `describes_dupocV`/`describes_botDupoc` (the `TD`/`TBD` towers), `describes_just7`
-- (the budget-slot `Just7 k`), `describesAbove_prudent`.
#print axioms cast_transposeCode
#print axioms cast_canonical
#print axioms quote_emb_canonicalMeta
#print axioms descVal_closed
#print axioms descVal_closed_T
#print axioms describes_closed
#print axioms dimcid_vs_closed
#print axioms Describes.above
#print axioms loebSound_pG_of_above
#print axioms dimcid_vs_described_above
#print axioms describes_botSV
#print axioms describes_dupocV
#print axioms describes_botDupoc
#print axioms describes_just7
#print axioms describesAbove_prudent

-- The defections, one per opponent (each: DIMCID plays D at fuel 2 AND finds its guard within `k`, all large `k`),
-- and the opponents' replies (`ebot_D_of_probes_D`: EBot's ladder ends in D when all three frozen probes see a
-- defection; `just7_else_V`/`just7_D_of_probe`: the budget-slot Just's else branch by soundness of a found guard,
-- `evalGraph_of_guard`).
#print axioms loeb_DIMCID_vs_botDB
#print axioms loeb_DIMCID_vs_botMirror
#print axioms loeb_DIMCID_vs_DBot_core
#print axioms loeb_DIMCID_vs_EBot_core
#print axioms loeb_DIMCID_vs_OBot_core
#print axioms loeb_DIMCID_vs_DupocBot_core
#print axioms loeb_DIMCID_vs_Dupoc
#print axioms loeb_DIMCID_vs_botDupocBot
#print axioms loeb_DIMCID_vs_botDupoc
#print axioms loeb_DIMCID_vs_Just7
#print axioms loeb_DIMCID_vs_PrudentBot_core
#print axioms progCode_CIMCIC_SV
#print axioms loeb_DIMCID_vs_CIMCIC_core
#print axioms ebot_D_of_probes_D
#print axioms just7_else_V
#print axioms just7_D_of_probe

-- The seven cells (engine value → `S'` value), each with the box form: DIMCID × DBot `(C, C)` → `(D, C)`
-- (`llm_outcome_DIMCID_vs_DBot`, floor); DIMCID × EBot `(C, C)` → `(D, D)` (`llm_outcome_DIMCID_vs_EBot`, floor +
-- unreadability); DIMCID × OBot `(C, D)` → `(D, D)` (`llm_outcome_DIMCID_vs_OBot`, probe-first floor);
-- DIMCID × DupocBot `(C, D)` AT EVERY `k` (`outcome_DIMCID_vs_DupocBot`, a UNIVERSAL engine theorem) → `(D, D)`
-- for all large `k` — the two proof systems contradict each other on this cell (Dupoc's guard "DIMCID cooperates
-- with me" is false ⇒ SND ⇒ D, `snd_DupocBot_vs_DIMCID_notFound`); DIMCID × JustBot `(C, D)` → `(D, D)`
-- (`llm_outcome_DIMCID_vs_JustBot`, floor; on the budget-slot `Just7 k`, DIMCID's half against the described
-- `Just7 k`, Just's half on `Just7 k` AND on the engine's code `snd_JustBot_vs_DIMCID_engine` — no `Describes`
-- for `progCode (JustBot k)`, ROUTE_B_SCOPE §7); DIMCID × PrudentBot `(C, D)` → `(D, D)` (`llm_outcome_DIMCID_vs_PrudentBot`,
-- floor; Prudent's outer guard false ⇒ D); CIMCIC × DIMCID `(D, C)` → `(D, D)` (`llm_outcome_CIMCIC_vs_DIMCID`,
-- floor; CIMCIC's guard self-refuting ⇒ D, `snd_CIMCIC_vs_DIMCID_notFound`). The row: `dimcid_flips_census`.
#print axioms loeb_DIMCID_vs_DBot
#print axioms loeb_DIMCID_vs_DBot_guard
#print axioms loeb_DIMCID_vs_EBot
#print axioms loeb_DIMCID_vs_EBot_guard
#print axioms loeb_DIMCID_vs_OBot
#print axioms loeb_DIMCID_vs_OBot_guard
#print axioms loeb_DIMCID_vs_DupocBot
#print axioms loeb_DIMCID_vs_DupocBot_guard
#print axioms snd_DupocBot_vs_DIMCID_notFound
#print axioms snd_JustBot_vs_DIMCID_engine
#print axioms loeb_DIMCID_vs_JustBot
#print axioms loeb_DIMCID_vs_Just7_guard
#print axioms loeb_DIMCID_vs_PrudentBot
#print axioms loeb_DIMCID_vs_PrudentBot_guard
#print axioms loeb_CIMCIC_vs_DIMCID
#print axioms loeb_DIMCID_vs_CIMCIC_guard
#print axioms snd_CIMCIC_vs_DIMCID_notFound
#print axioms dimcid_flips_census

-- THE FLOOR VERDICT PASS (Cells/FloorVerdicts, 2026-09-27) — every remaining engine floor cell without an `S'`
-- statement (24 cells: Dupoc × DBot/EBot/CupodTroll, Just × DBot/EBot/CupodTroll/Cupod/Prudent, CIMCIC ×
-- CupodTroll/Cupod/Prudent, Guardian × CIMCIC/Dupoc/Just/Prudent, Wary × Dupoc/Just/Prudent, Cupod × OBot/Prudent,
-- Prudent × Cupod/Dupoc/Prudent/EBot; plus the two `cenU` cells CIMCIC × DBot/EBot) is a GENUINE floor on at least one
-- side: the floor guard is a TRUE Σ₁ sentence whose only evaluation witness runs through the ELSE branch of a search
-- node with a FALSE guard σ, and `¬ LenBox TAct k ⌜σ⌝` is, up to an additive constant, the bounded consistency
-- statement `Con_TAct(k + c)` — a Pudlák-type lower-bound question (`k^ε` ≤ · ≤ poly(k); the linear case open), not
-- a fact this development settles. No (F)/(P) CELL, hence no cell theorem; what is unconditional: the SETTLED HALVES
-- (`floor_<L>_vs_<R>_left/_right`, the non-floor side's play at the engine's fuel) and the TRUE GUARDS
-- (`floor_<L>_vs_<R>_true`, the floor side's consulted sentence is true in ℕ — the residue is exactly its provability
-- within `k`). The two-searcher bistable cells (Wary × Dupoc/Just/Prudent, Cupod × Prudent both ways, Just × Cupod,
-- CIMCIC × Cupod) have no settled side; the four prudence floors record the inner guard's truth. Prudent × EBot:
-- EBot's cooperation needs Prudent's Löb cooperation with `.bot MirrorBot` (not built). Summary: `floor_settled_census`.
#print axioms pos_DupocBot_vs_botCB
#print axioms pos_botDupocBot_vs_botCB
#print axioms snd_JustBot_vs_botDB
#print axioms floor_DupocBot_vs_DBot_right
#print axioms floor_DupocBot_vs_DBot_true
#print axioms floor_DupocBot_vs_EBot_right
#print axioms floor_DupocBot_vs_EBot_true
#print axioms floor_DupocBot_vs_CupodTrollBot_right
#print axioms floor_DupocBot_vs_CupodTrollBot_true
#print axioms floor_JustBot_vs_DBot_right
#print axioms floor_JustBot_vs_DBot_true
#print axioms floor_JustBot_vs_EBot_right
#print axioms floor_JustBot_vs_EBot_true
#print axioms floor_JustBot_vs_CupodTrollBot_right
#print axioms floor_JustBot_vs_CupodTrollBot_true
#print axioms floor_CIMCIC_vs_CupodTrollBot_right
#print axioms floor_CIMCIC_vs_CupodTrollBot_true
#print axioms floor_CIMCIC_vs_DBot_right
#print axioms floor_CIMCIC_vs_DBot_true
#print axioms floor_CIMCIC_vs_EBot_right
#print axioms floor_CIMCIC_vs_EBot_true
#print axioms floor_GuardianBot_vs_CIMCIC_left
#print axioms floor_GuardianBot_vs_CIMCIC_true
#print axioms floor_GuardianBot_vs_DupocBot_left
#print axioms floor_GuardianBot_vs_DupocBot_true
#print axioms floor_GuardianBot_vs_JustBot_left
#print axioms floor_GuardianBot_vs_JustBot_true
#print axioms floor_GuardianBot_vs_PrudentBot_true
#print axioms floor_CupodBot_vs_OBot_right
#print axioms floor_CupodBot_vs_OBot_true
#print axioms floor_PrudentBot_vs_DupocBot_true
#print axioms floor_PrudentBot_vs_PrudentBot_true
#print axioms floor_JustBot_vs_PrudentBot_true
#print axioms floor_CIMCIC_vs_PrudentBot_true
#print axioms floor_settled_census

-- THE DICHOTOMY THEOREMS (Cells/FloorDichotomy, 2026-09-27) — the 26 genuine floors, hypothesis-free: for each cell,
-- with the HINGE `A_k = LenBox TAct k (guardCodeB (templateCode φ) (progCode me) (progCode opp) k)` (the evaluator's literal
-- guard clause for the floor side's outermost search node, written INLINE), `dich_<L>_vs_<R> : ∃ k₀, ∀ k > k₀,
-- (¬A_k → the engine's value) ∧ (A_k → the found-branch value)`, both worlds at the engine's fuel on the engine's codes.
-- The ELSE world is the verdict pass's settled half + the search-else clause; the THEN world is the then-branch + the
-- partner's play, recovered where needed by SOUNDNESS of the found hinge and the evaluator's determinism
-- (`found_of_search_play`, `play_of_found_*`). Two- and three-hinge cells (the bistable pairs Wary × Dupoc/Just/Prudent,
-- Cupod × Prudent both ways, Just × Cupod, CIMCIC × Cupod; the prudence floors Just/CIMCIC/Guardian × Prudent) are NESTED
-- dichotomies with every determined case proved; Prudent's prudence guard is a hinge of its own where the verdict pass
-- rated it (P) (its `k̂`-chain is not built), proved FOUND against EBot (`prudence_found_vs_EBot`); Prudent × EBot's ELSE
-- world settles Prudent's side only (EBot's C there is the unbuilt Löb Prudent × `.bot MirrorBot`). THE REDUCTION
-- (`hinge_reduces_to_bounded_consistency_DupocBot_vs_DBot`): the hinge of Dupoc × DBot within `k` gives a `TAct`-proof
-- within `k + C₀ + C₁·size k` of `negTwin(k)` = "σ_k or its τ-twin is not provable within `k`" (σ_k = Dupoc's guard
-- against `.bot DefectBot`, FALSE in ℕ; at ℕ the disjuncts coincide, `negTwin_true_iff`, so the sentence says `¬□_k σ_k`
-- — a bounded-consistency instance); the CONVERSE from the conjunction (`bounded_consistency_reduces_to_hinge_…`), by the
-- evaluator's determinism inside `TAct` (`tact_conjTwin_imp_rDB`). No side taken: `S'` proves the dependence.
#print axioms hingeB
#print axioms found_of_search_play
#print axioms not_found_of_search_play
#print axioms play_of_found_opp_self
#print axioms play_of_found_opp_bot
#print axioms play_of_found_neg
#print axioms play_of_found_cimcic
#print axioms prudent_total
#print axioms cimcic_total
#print axioms ebot_total
#print axioms dich_DupocBot_vs_DBot
#print axioms dich_DupocBot_vs_EBot
#print axioms dich_DupocBot_vs_CupodTrollBot
#print axioms dich_JustBot_vs_DBot
#print axioms dich_JustBot_vs_EBot
#print axioms dich_JustBot_vs_CupodTrollBot
#print axioms dich_CIMCIC_vs_CupodTrollBot
#print axioms dich_CIMCIC_vs_DBot
#print axioms dich_CIMCIC_vs_EBot
#print axioms dich_GuardianBot_vs_CIMCIC
#print axioms dich_GuardianBot_vs_DupocBot
#print axioms dich_GuardianBot_vs_JustBot
#print axioms dich_CupodBot_vs_OBot
#print axioms dich_PrudentBot_vs_DupocBot
#print axioms dich_PrudentBot_vs_PrudentBot
#print axioms prudent_of_verdicts
#print axioms dich_JustBot_vs_PrudentBot
#print axioms dich_CIMCIC_vs_PrudentBot
#print axioms dich_GuardianBot_vs_PrudentBot
#print axioms tact_EBot_D_vs_botDB
#print axioms prudence_found_closed
#print axioms prudence_found_vs_EBot
#print axioms dich_PrudentBot_vs_EBot
#print axioms dich_WaryBot_vs_DupocBot
#print axioms dich_WaryBot_vs_JustBot
#print axioms dich_WaryBot_vs_PrudentBot
#print axioms dich_CupodBot_vs_PrudentBot_core
#print axioms dich_CupodBot_vs_PrudentBot
#print axioms dich_PrudentBot_vs_CupodBot
#print axioms dich_JustBot_vs_CupodBot
#print axioms dich_CIMCIC_vs_CupodBot
#print axioms cast_DBot
#print axioms transposeCode_DBotV
#print axioms dbot_C_of_probe_D_V
#print axioms dbotT_D_of_probe_C_V
#print axioms probe_of_dbot_C_V
#print axioms probe_of_dbotT_D_V
#print axioms not_found_of_SV_play
#print axioms dupoc_else_V
#print axioms cupod_else_V
#print axioms guardCode_DuB1
#print axioms guardCode_DuB1_swap
#print axioms guardCode_rDB
#print axioms eval_boxK_iff
#print axioms eval_negTwin_iff
#print axioms eval_conjTwin_iff
#print axioms tact_rDB_imp_negTwin
#print axioms tact_conjTwin_imp_rDB
#print axioms hinge_DupocBot_vs_DBot_eq
#print axioms hinge_reduces_to_bounded_consistency_DupocBot_vs_DBot
#print axioms bounded_consistency_reduces_to_hinge_DupocBot_vs_DBot
#print axioms substs_lMap_swap_binNumeralMeta
#print axioms negTwin_true_iff

-- THE PRUDENCE `k̂`-CHAIN (Cells/PrudentLoose §1–3, 2026-09-27) — Prudent's prudence guard `B_k` ("the opponent defects
-- against `.bot DefectBot`") DISCHARGED where the verdict pass rated it (P): against an engine searcher `SV g a k` the
-- guard is the `binNumeral k`-instance of the fixed formula `qPiS g a` (Prudent described above `KP`, the opponent by its
-- canonical `SV` triple; the me-slots inert), TRUE in every model above a threshold when the opponent's defection
-- against the probe is its THEN-branch (Guardian: a true closed atom, `guardian_botDB_V`; Wary: the Π₁ truth of its
-- `.neg` guard, `wary_botDB_V`; Cupod: `cupod_botDB_V`; the τ-twins `guardianT/waryT_botCB_V`, `dupoc_botCB_V` for the
-- swapped reading), so `TAct ⊢ ∀¹ (k̂ ≤ #0 🡒 qPiS g a)` by completeness and the instance fits `k` for all large `k`
-- (`prudence_found_of_SV`, `found_of_all_above`). Engine-code forms `prudence_found_vs_GuardianBot/_WaryBot/_CupodBot`;
-- the four nested dichotomies RESTATED with `B` gone (`dich_…_prudenceFound`, only the remaining hinge(s) inline; the
-- originals in Cells/FloorDichotomy untouched). NOT discharged, on purpose: Just × Prudent and CIMCIC × Prudent — there
-- the opponent's defection against `.bot DefectBot` is its ELSE-branch, so `B_k` is a bounded-consistency-type sentence
-- (true in ℕ, NOT in every model of `TAct`), the (G) residue of the verdict pass; for Just there is also §7 (no fixed
-- formula describes `progCode (JustBot k)`). Both keep `B` as a hinge.
#print axioms qGB1
#print axioms guardCode_GB1
#print axioms tact_qGB1
#print axioms guardian_botDB_V
#print axioms tact_qGTB0
#print axioms guardianT_botCB_V
#print axioms wary_botDB_V
#print axioms tact_qWTB0
#print axioms waryT_botCB_V
#print axioms guardCode_PiS
#print axioms eval_qPiS_iff_V
#print axioms eval_qPiS_swap_iff_V
#print axioms tact_qPiS_above
#print axioms prudence_found_of_SV
#print axioms prudence_found_vs_GuardianBot
#print axioms prudence_found_vs_WaryBot
#print axioms prudence_found_vs_CupodBot
#print axioms dich_GuardianBot_vs_PrudentBot_prudenceFound
#print axioms dich_WaryBot_vs_PrudentBot_prudenceFound
#print axioms dich_CupodBot_vs_PrudentBot_prudenceFound
#print axioms dich_PrudentBot_vs_CupodBot_prudenceFound

-- PRUDENT × `.bot MirrorBot` BY LÖB (Cells/PrudentLoose §4, 2026-09-27) — Cells/PrudentMirror's family at the CLOSED
-- opponent `pBot Mirror` (`describes_closed`): `qPB1` ("`.bot MirrorBot` plays C against Prudent k"), `qPB2` (the prudence
-- conjunct "`.bot MirrorBot` plays D against `.bot DefectBot`", a closed Σ₁ fact), their τ-twins, the family
-- `pPB = (qPB1 ⋏ qPB2) ⋏ (τqPB1 ⋏ τqPB2)`, `loebSound_pPB : LoebSound pPB (14 + KP) 16` (∧-elimination hands each searcher
-- both guards; `.bot MirrorBot` copies at fuel 5 — the `.bot` step + Mirror's sim step, `botMirror_step_V`; the prudence
-- facts at fuel 4), `family_found` at `boundedInnerNec_sixteen`. `loeb_PrudentBot_vs_botMirror`: for all large `k`,
-- `EvalGraph 3 (progCode (PrudentBot k)) (pBot Mirror) … C ∧ EvalGraph 5 (pBot Mirror) (progCode (PrudentBot k)) … C` — the `S'`
-- twin of the engine's `prudent_botmirror_coop`; the box form of both guards; the τ-twin `(D, D)`.
#print axioms botMirror_step_V
#print axioms botMirror_copies3_V
#print axioms botMirror_botDB_V
#print axioms botMirror_botCB_V
#print axioms prudent_search_any_V
#print axioms prudentT_search_any_V
#print axioms guardCode_PB1
#print axioms guardCode_PB2
#print axioms guardCode_PB1T
#print axioms guardCode_PB2T
#print axioms eval_qPB1_iff_V
#print axioms eval_qPB2_iff_V
#print axioms eval_qPB1T_iff_V
#print axioms eval_qPB2T_iff_V
#print axioms pPB_all_V
#print axioms pPB_guards_V
#print axioms loebSound_pPB
#print axioms loeb_Prudent_vs_botMirror_core
#print axioms loeb_PrudentBot_vs_botMirror
#print axioms loeb_PrudentBot_vs_botMirror_guards
#print axioms loeb_PrudentT_vs_botMirror

-- PRUDENT × EBOT CLOSED IN BOTH WORLDS (Cells/PrudentLoose §5, 2026-09-27) — EBot's ladder against `PrudentBot k`: rung 1
-- (`.bot DefectBot`) and rung 2 (`.bot CooperateBot`) Prudent defects (SND), rung 3 (`.bot MirrorBot`) Prudent COOPERATES
-- (the Löb above), so EBot cooperates (`ebot_C_of_probes3`) whatever Prudent's outer verdict: `floor_PrudentBot_vs_EBot_right`
-- (the settled half, pad 7) and `dich_PrudentBot_vs_EBot_full : ∃ k₀, ∀ k > k₀, (¬A_k → (D, C)) ∧ (A_k → (C, C))` — the
-- `¬A_k` world is now the engine's full `(D, C)` (`dich_PrudentBot_vs_EBot` had Prudent's side only).
#print axioms ebot_C_of_probes3
#print axioms floor_PrudentBot_vs_EBot_right
#print axioms dich_PrudentBot_vs_EBot_full

end ArithS
