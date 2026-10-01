import ArithS.Tau.Rows.Coop
import ArithS.Tau.Rows.Defect
import ArithS.Tau.Rows.TftSim
import ArithS.Tau.Rows.DBot
import ArithS.Tau.Rows.OBot
import ArithS.Tau.Rows.CupodTroll
import ArithS.Tau.Rows.EBot
import ArithS.Tau.Described

/-!
# ArithS.Audit.Tau — the census of the tau layer (Phase 3 of `SPRIME_SOURCE_OF_TRUTH.md`)

The `S'` tau rows (`RowSpecA`, `Tau/Spec.lean`) and floor bits (`FloorBitA`) of the seven search-free / SND / POS
templates, with the column kit they rest on (`Tau/Columns.lean`). Each line must read
`[propext, Classical.choice, Quot.sound]`.
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

end ArithS.Tau
