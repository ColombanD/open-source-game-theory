import ArithS.Tau.Rows.Coop
import ArithS.Tau.Rows.Defect
import ArithS.Tau.Rows.TftSim
import ArithS.Tau.Rows.DBot
import ArithS.Tau.Rows.OBot
import ArithS.Tau.Rows.CupodTroll
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
import ArithS.Tau.Quine
import ArithS.Tau.ClosedProbe
import ArithS.Tau.NeverFits
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
on defection, CIMCIC's tautology), and (Phase 3c/3d) the entangled `.sys` bits folded into those rows: 14 rows,
47 floor bits, 191/196 paper bits. Each line must read `[propext, Classical.choice, Quot.sound]`.
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

-- Phase 3b — the length obstruction (`Tau/NeverFits.lean`): a `.self`-guard over a budget-carrying frozen
-- instance is longer than its budget; the six slots it decides.
#print axioms le_quote_sentence_of_FOccC
#print axioms binNumeral_le_templateCode_selfBot
-- Phase 2c (2026-10-01): the obstruction is stated on the explicit pre-abstraction code `pBot (pSearch k' (templateCode φ) p q)`;
-- the tau slots it decided (`cimcic_tftSim_D`, `cimcic_ebot_D`, `dimcid_tftSim_C`, `dimcid_ebot_C`) are UNSTATED until
-- Phase 3e re-proves them with the table's values on the budget-abstracted stored templates.
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

end ArithS.Tau
