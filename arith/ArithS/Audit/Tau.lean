import ArithS.Tau.Rows.Coop
import ArithS.Tau.Rows.Defect
import ArithS.Tau.Rows.TftSim
import ArithS.Tau.Rows.DBot
import ArithS.Tau.Rows.OBot
import ArithS.Tau.Rows.CupodTroll
import ArithS.Tau.Rows.DupocTroll
import ArithS.Tau.Rows.Dimdid
import ArithS.Tau.Rows.EBot
import ArithS.Tau.Described
import ArithS.Tau.Entangled.Base
import ArithS.Tau.Entangled.Order
import ArithS.Tau.Entangled.Tower
import ArithS.Tau.Entangled.Family
import ArithS.Tau.Entangled.Loeb
import ArithS.Tau.Entangled.Congr
import ArithS.Tau.Entangled.Dimcid
import ArithS.Tau.Entangled.DupocDupoc
import ArithS.Tau.Entangled.DimcidDupoc
import ArithS.Tau.Entangled.DimcidCupod
import ArithS.Tau.Entangled.DimcidCimcic
import ArithS.Tau.Entangled.DupocCimcic
import ArithS.Tau.Entangled.DupocPrudent
import ArithS.Tau.Entangled.CupodPrudent
import ArithS.Tau.Entangled.CimcicPrudent
import ArithS.Tau.Entangled.CupodCimcic
import ArithS.Tau.Entangled.DupocCupod
import ArithS.Tau.Entangled.Mirror
import ArithS.Tau.Entangled.EBotPrudent
import ArithS.Tau.Entangled.Generic
import ArithS.Tau.Entangled.DimcidPrudent
import ArithS.Tau.Entangled.DimdidSys
import ArithS.Tau.Dimdid
import ArithS.Tau.ClosedWatchDd
import ArithS.Tau.Quine
import ArithS.Tau.ClosedProbe
import ArithS.Tau.Watch
import ArithS.Tau.Stored
import ArithS.Tau.ClosedWatch
import ArithS.Tau.Watch2
import ArithS.Tau.ClosedWatch2
import ArithS.Tau.Watch3
import ArithS.Tau.ClosedWatch3
import ArithS.Tau.NeverFits
import ArithS.Tau.NeverFitsSys
import ArithS.Tau.Rows.Dupoc
import ArithS.Tau.Rows.Cupod
import ArithS.Tau.Rows.CIMCIC
import ArithS.Tau.Rows.DIMCID
import ArithS.Tau.Rows.Prudent
import ArithS.Tau.Rows.MaxConfidence
import ArithS.Tau.Rows.MinConfidence

/-!
# ArithS.Audit.Tau — the census of the tau layer (Phase 3 of `SPRIME_SOURCE_OF_TRUTH.md`)

The `S'` tau rows (`RowSpecA`, `Tau/Spec.lean`) and floor bits (`FloorBitA`) of the seven search-free / SND / POS
templates, with the column kit they rest on (`Tau/Columns.lean`), (Phase 3b) the NON-entangled slots of the
seven self-probers' rows with the diagonal kit they rest on (`Tau/Quine.lean`: the Löb quines, DIMCID's fixpoint
on defection, CIMCIC's tautology), (Phase 3c/3d) the entangled `.sys` bits folded into those rows, and (Phase 3e)
the ten bits route (c) made generic recovers — the guards over a closed budget-carrying watch and the
`dimcid × prudent` systems, and (Phase 3f, decision (α)) the last bit `dimcid × ebot` — τ(EBot)'s three-stage watch
over the system `inst dimcid mirror`, described with its member's budget in the slot since the abstraction descends
into systems (`Tau/Watch3.lean`, `Tau/ClosedWatch3.lean`): 14 rows, 149 row slots, 47 floor bits, 196/196 paper
bits. Each line must read `[propext, Classical.choice, Quot.sound]`.
-/

namespace ArithS.Tau

-- The column kit: closed guards found / not found in any frame, the self-refuting CIMCIC instance.
#print axioms closed_found
#print axioms probe_const_found
#print axioms probe_const_not_found
#print axioms eq_const_found
#print axioms eq_const_not_found
#print axioms cimcic_defect_not_found
#print axioms col_dupoc_coop
#print axioms col_cupod_defect

-- The instance's own description (`Tau/Described.lean`): the two POS bits and the DIMCID FLIP.
#print axioms found_implC_self
#print axioms col_cimcic_coop
#print axioms col_dimcid_defect
#print axioms loebSound_pDiI
#print axioms dimcid_coop_found
#print axioms col_dimcid_coop

-- The seven rows.
#print axioms coopRowSpecA
#print axioms defectRowSpecA
#print axioms tftSimRowSpecA
#print axioms dbotRowSpecA
#print axioms obotRowSpecA
#print axioms cupodTrollRowSpecA
#print axioms dupocTrollRowSpecA
#print axioms ebotRowSpecA

-- The thirteen floor bits (settled on this side; the partner's hinge).
#print axioms dbotRowSpecA_dupoc_floor
#print axioms dbotRowSpecA_cimcic_floor
#print axioms dbotRowSpecA_maxconfidence_floor
#print axioms dbotRowSpecA_minconfidence_floor
#print axioms obotRowSpecA_cupod_floor
#print axioms cupodTrollRowSpecA_dupoc_floor
#print axioms cupodTrollRowSpecA_cimcic_floor
#print axioms cupodTrollRowSpecA_maxconfidence_floor
#print axioms cupodTrollRowSpecA_minconfidence_floor
#print axioms dupocTrollRowSpecA_cimcic_floor
#print axioms ebotRowSpecA_dupoc_floor
#print axioms ebotRowSpecA_cimcic_floor
#print axioms ebotRowSpecA_maxconfidence_floor
#print axioms ebotRowSpecA_minconfidence_floor

-- Phase 3b — the diagonal kit (`Tau/Quine.lean`).
#print axioms guardCode_botSV_self_eq_instB_V
#print axioms guardCode_botSV_self_swap_eq_instB_V
#print axioms loebSound_quine
#print axioms quine_found
#print axioms loebSound_dimQ
#print axioms dimcid_quine_found
#print axioms tact_qInst_cimQ
#print axioms cimcic_quine_found
#print axioms probe_not_found_of_bit
#print axioms cimcic_obot_not_found
#print axioms tact_qInst_eq_const
#print axioms botSV_found_V
#print axioms tact_qCT_above
#print axioms cupod_cupodTroll_found
-- 2026-10-19 — the `dupocTroll` slot (the Dupoc-hunting troll): the troll's bits, Dupoc's and the natives' theorem
-- slots (SND, the troll defects on them), Cupod's C, Prudent's D, DIMCID's flip D.
#print axioms dupocTroll_C
#print axioms dupocTroll_rec_D
#print axioms dupoc_dupocTroll_D
#print axioms maxconfidence_dupocTroll_D
#print axioms minconfidence_dupocTroll_D
#print axioms cupod_dupocTroll_C
#print axioms prudent_dupocTroll_D
#print axioms dimcid_dupocTroll_D
-- 2026-10-19 — τ(DIMDID) (`Tau/Dimdid.lean`, `Tau/Entangled/DimdidSys.lean`, `Tau/ClosedWatchDd.lean`,
-- `Tau/Rows/Dimdid.lean`): the transposition bridge, the two columns, the self-defeating guard, the mutual families
-- aligned on defection, the OBot flip (POS on the two-stage watch), the EBot slot (fragment-free), the row and its
-- five floor bits, and the ten partner-side floor bits / theorem slots.
#print axioms bitPlays_transpose
#print axioms col_dimdid_coop
#print axioms col_dimdid_defect
#print axioms dimdid_not_found_of_C
#print axioms dimdid_tftSim_C
#print axioms dimdid_dbot_C
#print axioms dimdid_cupodTroll_C
#print axioms dimdid_dupocTroll_C
#print axioms Sys2.loebSound_CDd
#print axioms Sys2.loebSound_DdDi
#print axioms ent_dimdid_cupod
#print axioms ent_cupod_dimdid
#print axioms ent_dimdid_dimcid
#print axioms ent_dimcid_dimdid
#print axioms dimdid_obot_D
#print axioms dimdid_ebot_C
#print axioms dimdid_quine_D
#print axioms dimdidRowSpecA
#print axioms dimdidRowSpecA_dupoc_floor
#print axioms dimdidRowSpecA_maxconfidence_floor
#print axioms dimdidRowSpecA_minconfidence_floor
#print axioms dimdidRowSpecA_cimcic_floor
#print axioms dimdidRowSpecA_prudent_floor
#print axioms dupocRowSpecA_dimdid_floor
#print axioms maxconfidenceRowSpecA_dimdid_floor
#print axioms minconfidenceRowSpecA_dimdid_floor
#print axioms cimcicRowSpecA_dimdid_floor
#print axioms prudentRowSpecA_dimdid_floor

-- Phase 3b — the length obstruction (`Tau/NeverFits.lean`): a `.self`-guard over a budget-carrying frozen
-- instance is longer than its budget; the six slots it decides.
#print axioms le_quote_sentence_of_FOccC
#print axioms binNumeral_le_templateCode_selfBot
-- Phase 2c (2026-10-01): the obstruction is stated on the explicit pre-abstraction code `pBot (pSearch k' (templateCode φ) p q)`;
-- the tau slots it decided are re-proved with the table's values on the budget-abstracted stored templates (Phase 3e,
-- below; `dimcid × ebot` in Phase 3f, `Tau/ClosedWatch3.lean`).
#print axioms selfBot_guard_not_found
#print axioms size_canonical_le_formulaLenMeta_sentenceAt_self
#print axioms selfBot_guard_never_fits
#print axioms cimcic_selfBot_D
#print axioms dimcid_selfBot_C

-- The seven self-probers' rows (non-entangled slots).
#print axioms dupocRowSpecA
#print axioms cupodRowSpecA
#print axioms cimcicRowSpecA
#print axioms dimcidRowSpecA
#print axioms prudentRowSpecA
#print axioms maxconfidenceRowSpecA
#print axioms minconfidenceRowSpecA

-- The floor-SIDE floor bits (the hinge is the row bot's own guard).
#print axioms dupocRowSpecA_ebot_floor
#print axioms dupocRowSpecA_dbot_floor
#print axioms dupocRowSpecA_cupodTroll_floor
#print axioms cupodRowSpecA_obot_floor
#print axioms cimcicRowSpecA_ebot_floor
#print axioms cimcicRowSpecA_dbot_floor
#print axioms cimcicRowSpecA_cupodTroll_floor
#print axioms cimcicRowSpecA_dupocTroll_floor
#print axioms prudentRowSpecA_ebot_floor
#print axioms prudentRowSpecA_prudent_floor
#print axioms maxconfidenceRowSpecA_ebot_floor
#print axioms maxconfidenceRowSpecA_dbot_floor
#print axioms maxconfidenceRowSpecA_cupodTroll_floor
#print axioms minconfidenceRowSpecA_ebot_floor
#print axioms minconfidenceRowSpecA_dbot_floor
#print axioms minconfidenceRowSpecA_cupodTroll_floor

-- The system floor bits folded into the rows (Phase 3d; the proof terms are the `entFloor_*` lemmas below).
#print axioms dupocRowSpecA_cupod_floor
#print axioms dupocRowSpecA_prudent_floor
#print axioms maxconfidenceRowSpecA_cupod_floor
#print axioms maxconfidenceRowSpecA_prudent_floor
#print axioms minconfidenceRowSpecA_cupod_floor
#print axioms minconfidenceRowSpecA_prudent_floor
#print axioms cupodRowSpecA_dupoc_floor
#print axioms cupodRowSpecA_maxconfidence_floor
#print axioms cupodRowSpecA_minconfidence_floor
#print axioms cupodRowSpecA_cimcic_floor
#print axioms cupodRowSpecA_prudent_floor
#print axioms cimcicRowSpecA_cupod_floor
#print axioms cimcicRowSpecA_prudent_floor
#print axioms prudentRowSpecA_dupoc_floor
#print axioms prudentRowSpecA_maxconfidence_floor
#print axioms prudentRowSpecA_minconfidence_floor
#print axioms prudentRowSpecA_cupod_floor
#print axioms prudentRowSpecA_cimcic_floor
#print axioms ebotRowSpecA_prudent_floor

-- The entangled bits (`Tau/Entangled/*`): the system kit, the Löb families, the 23 theorem bits and the 19 floor bits
-- (all folded into the rows above since Phase 3d).
#print axioms Sys2.canonical_code
#print axioms Sys2.describesBot
#print axioms Sys2.describesMem
#print axioms guardCodeB_sysClose_eq_instB
#print axioms Sys2.guard_eq_instB
#print axioms Sys2.q_congr_opp_impl
#print axioms loebSound_pQ₂_above
#print axioms boxes_pQ₂_nat
#print axioms loebSound_DD
#print axioms found_DD
#print axioms ent_dupoc_maxconfidence
#print axioms ent_maxconfidence_dupoc
#print axioms ent_dupoc_minconfidence
#print axioms ent_minconfidence_dupoc
#print axioms ent_maxconfidence_minconfidence
#print axioms ent_minconfidence_maxconfidence
#print axioms Sys2.loebSound_Di
#print axioms Sys2.found_Di
#print axioms ent_dimcid_dupoc
#print axioms ent_dimcid_maxconfidence
#print axioms ent_dimcid_minconfidence
#print axioms ent_dupoc_dimcid
#print axioms ent_maxconfidence_dimcid
#print axioms ent_minconfidence_dimcid
#print axioms ent_dimcid_cupod
#print axioms boxConseq_CDi
#print axioms ent_cupod_dimcid
#print axioms ent_dimcid_cimcic
#print axioms ent_cimcic_dimcid
#print axioms Sys2.loebSound_DCi
#print axioms ent_dupoc_cimcic
#print axioms ent_maxconfidence_cimcic
#print axioms ent_minconfidence_cimcic
#print axioms ent_cimcic_dupoc
#print axioms ent_cimcic_maxconfidence
#print axioms ent_cimcic_minconfidence
#print axioms entFloor_dupoc_prudent
#print axioms entFloor_maxconfidence_prudent
#print axioms entFloor_minconfidence_prudent
#print axioms entFloor_prudent_dupoc
#print axioms entFloor_prudent_maxconfidence
#print axioms entFloor_prudent_minconfidence
#print axioms entFloor_cupod_prudent
#print axioms entFloor_prudent_cupod
#print axioms entFloor_cimcic_prudent
#print axioms entFloor_prudent_cimcic
#print axioms entFloor_cupod_cimcic
#print axioms entFloor_cimcic_cupod
#print axioms entFloor_dupoc_cupod
#print axioms entFloor_maxconfidence_cupod
#print axioms entFloor_minconfidence_cupod
#print axioms entFloor_cupod_dupoc
#print axioms entFloor_cupod_maxconfidence
#print axioms entFloor_cupod_minconfidence
#print axioms Sys2c.loebSound_Di
#print axioms Sys2c.found_Di
#print axioms col_dimcid_mirror_D
#print axioms ent_ebot_dimcid
#print axioms Sys2n.member_then2_V
#print axioms loebSound_PMi
#print axioms found_PMi
#print axioms col_prudent_mirror_C
#print axioms ent_ebot_prudent
#print axioms entFloor_ebot_prudent

-- Phase 3e — a bot-wrapped simple searcher and a run-stage watch over it as `k̂`-towers (`Tau/Watch.lean`), the
-- stored (budget-abstracted) template of a guard over a closed watch (`Tau/Stored.lean`).
#print axioms SM.describesBot
#print axioms W1.sim_gain
#print axioms W1.code_lt_tr
#print axioms W1.describesBot
#print axioms codeTermMetaAbs_botW1
#print axioms eval_closedDescAt_some_V
#print axioms eval_plAt_self_closed
#print axioms eval_plAt_closed_self
#print axioms eval_plAt_closed_closed
#print axioms guardCodeB_plain_eq_instB
#print axioms W1.closedDescAt_code
#print axioms W1.absVal_code
#print axioms W1.absVal_tr_code
#print axioms closedDescAt_botSV
#print axioms absVal_botSV
#print axioms absVal_tr_botSV

-- Phase 3e — guards over a closed budget-carrying watch, FOUND (`Tau/ClosedWatch.lean`): DIMCID's self-fulfilling
-- family on the watch, the POS-above chain, the seven bits.
#print axioms isSemiformula7_cast_templateAt
#print axioms W1.describesBotT
#print axioms describes_botSVT
#print axioms dimcid_closed_found
#print axioms plain_found_above
#print axioms tact_qCi_above
#print axioms tact_qPr_above
#print axioms ofSearch_self_plays
#print axioms ofSearch_tr_self_plays
#print axioms tact_qInst_prC
#print axioms dimcid_D_of_W1
#print axioms dimcid_D_of_SV
#print axioms dimcid_tftSim_D
#print axioms dimcid_dbot_D
#print axioms dimcid_cupodTroll_D
#print axioms cimcic_C_of_W1
#print axioms dupoc_C_of_W1
#print axioms cimcic_tftSim_C
#print axioms dupoc_tftSim_C
#print axioms maxconfidence_tftSim_C
#print axioms minconfidence_tftSim_C

-- Phase 3e — the two-stage watch (τ(OBot)'s instance at a self-prober): the gain calculus, the τ-order of the
-- cascade, its tower and stored description (`Tau/Watch2.lean`), and the bit (`Tau/ClosedWatch2.lean`).
#print axioms Gain.ppair_right
#print axioms Gain.ppair_left
#print axioms Gain.bot
#print axioms W1.gain
#print axioms W1.sim_le_code
#print axioms W2.code_lt_tr
#print axioms W2.describesBot
#print axioms W2.describesBotT
#print axioms W2.closedDescAt_code
#print axioms W2.absVal_code
#print axioms W2.absVal_tr_code
#print axioms dimcid_D_of_towers
#print axioms dimcid_obot_D

-- Phase 3e — two-member systems given by member towers (`Tau/Entangled/Generic.lean`) and the `dimcid × prudent`
-- systems (`Tau/Entangled/DimcidPrudent.lean`): the τ-order of the mixed lists, Prudent's member at DIMCID on a
-- constant inner template, the two bits.
#print axioms MT.ofSM_ok
#print axioms Sys2m.canonical_code
#print axioms Sys2m.guard_eq_instB_of
#print axioms Sys2m.tr_guard_eq_instB_of
#print axioms Sys2m.eval_q_impl
#print axioms Sys2m.eval_q_impl_swap
#print axioms simple_member_then_V
#print axioms Sys2m.loebSound_Di
#print axioms Sys2m.found_Di
#print axioms nested_gain
#print axioms nested_dominates
#print axioms MT.ofNM_ok
#print axioms Sys2m.ofSN_ok
#print axioms Sys2m.ofNS_ok
#print axioms templateAt_probeD_dimcid_defect
#print axioms PMd_code_nat
#print axioms found_DiP_engine
#print axioms ent_dimcid_prudent
#print axioms prudent_probe_dimcid_not_found
#print axioms ent_prudent_dimcid

-- Phase 3f (decision (α), 2026-10-02) — the last bit, `dimcid × ebot = D`. The abstraction descends into systems
-- (`Agents/CodeTermAbs.codeTermMetaAbs_sys`), so the mirror system's tower is its abstracted description
-- (`codeTermMetaAbs_Sys2c`); the three-stage watch `W3` is a `k̂`-tower (`cascade_gain`: one more run-stage keeps
-- a gain), its stored description constant; DIMCID's guard does not read the opponent slots (`gDi_subst_congr`),
-- which replaces the `fragF` step of `dimcid_D_of_towers` (the watch contains a `.sys`).
#print axioms cascade_gain
#print axioms codeTermMetaAbs_Sys2c
#print axioms W3.code_lt_tr
#print axioms W3.describesBot
#print axioms W3.closedDescAt_code
#print axioms W3.absVal_code
#print axioms W3.absVal_tr_code
#print axioms gDi_subst_congr
#print axioms qPlain_gDi_opp
#print axioms dimcid_D_of_towers'
#print axioms dimcid_ebot_D

-- `Tau/NeverFitsSys.lean`, restated on the UNABSTRACTED template (as `Tau/NeverFits.lean` was in Phase 2c): a
-- `.self`-guard over a watch that freezes a budget-carrying SYSTEM, stored VERBATIM, never fits. No compiled instance
-- stores that template; `dimcid_ebot_C` (true under Phase 2c's coding, FALSE since Phase 2d) is gone.
#print axioms binNumeral_le_codeTerm_of_hasSysC
#print axioms binNumeral_le_templateCode_selfBot_sys
#print axioms selfBot_sys_guard_not_found
#print axioms dimcid_selfBot_sys_C

end ArithS.Tau
