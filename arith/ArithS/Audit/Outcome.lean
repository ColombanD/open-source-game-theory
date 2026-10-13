import ArithS.Outcome.Spec
import ArithS.Cells.RedCellEngine
import ArithS.Outcome.Matrix.CIMCIC
import ArithS.Outcome.Matrix.CooperateBot
import ArithS.Outcome.Matrix.CupodBot
import ArithS.Outcome.Matrix.CupodTrollBot
import ArithS.Outcome.Matrix.DBot
import ArithS.Outcome.Matrix.DIMCID
import ArithS.Outcome.Matrix.DIMDID
import ArithS.Outcome.Matrix.DefectBot
import ArithS.Outcome.Matrix.DupocBot
import ArithS.Outcome.Matrix.DupocTrollBot
import ArithS.Outcome.Matrix.EBot
import ArithS.Outcome.Matrix.GuardianBot
import ArithS.Outcome.Matrix.JustBot
import ArithS.Outcome.Matrix.MirrorBot
import ArithS.Outcome.Matrix.OBot
import ArithS.Outcome.Matrix.PrudentBot
import ArithS.Outcome.Matrix.TitForTatBot
import ArithS.Outcome.Matrix.WaryBot
import ArithS.Outcome.Floors

/-!
# ArithS.Audit.Outcome — the census of the outcome layer

Every cell of `Outcome/Matrix/*.lean` (the engine-shaped statements), the engine-level red cell, and the 26
engine-side floor halves of `Outcome/Floors.lean` (`FloorSpecA`, one per `dich_<L>_vs_<R>`).
-/

namespace ArithS

#print axioms guard_DupocBot_iff_guard_CupodBot
#print axioms snd_DupocBot_vs_CupodBot
#print axioms outcome_CIMCIC_vs_CIMCIC
#print axioms outcome_CIMCIC_vs_DIMCID
#print axioms outcome_CIMCIC_vs_MirrorBot
#print axioms outcome_CIMCIC_vs_TitForTatBot
#print axioms outcome_CIMCIC_vs_CooperateBot
#print axioms outcome_CIMCIC_vs_DefectBot
#print axioms outcome_CIMCIC_vs_OBot
#print axioms outcome_CIMCIC_vs_DupocBot
#print axioms outcome_CIMCIC_vs_JustBot
#print axioms outcome_CooperateBot_vs_CooperateBot
#print axioms outcome_CooperateBot_vs_DefectBot
#print axioms outcome_CupodBot_vs_CooperateBot
#print axioms outcome_CupodBot_vs_DBot
#print axioms outcome_CupodBot_vs_DefectBot
#print axioms outcome_CupodBot_vs_EBot
#print axioms outcome_CupodBot_vs_TitForTatBot
#print axioms outcome_CupodBot_vs_MirrorBot
#print axioms outcome_CupodBot_vs_CupodBot
#print axioms outcome_CupodTrollBot_vs_CooperateBot
#print axioms outcome_CupodTrollBot_vs_CupodBot
#print axioms outcome_CupodTrollBot_vs_CupodTrollBot
#print axioms outcome_CupodTrollBot_vs_DBot
#print axioms outcome_CupodTrollBot_vs_DefectBot
#print axioms outcome_CupodTrollBot_vs_EBot
#print axioms outcome_CupodTrollBot_vs_MirrorBot
#print axioms outcome_CupodTrollBot_vs_OBot
#print axioms outcome_CupodTrollBot_vs_TitForTatBot
#print axioms outcome_DBot_vs_CooperateBot
#print axioms outcome_DBot_vs_DBot
#print axioms outcome_DBot_vs_DefectBot
#print axioms outcome_DIMCID_vs_DBot
#print axioms outcome_DIMCID_vs_DIMCID
#print axioms outcome_DIMCID_vs_EBot
#print axioms outcome_DIMCID_vs_MirrorBot
#print axioms outcome_DIMCID_vs_OBot
#print axioms outcome_DIMCID_vs_PrudentBot
#print axioms outcome_DIMCID_vs_TitForTatBot
#print axioms outcome_DIMCID_vs_CooperateBot
#print axioms outcome_DIMCID_vs_DefectBot
#print axioms outcome_DIMCID_vs_DupocBot
#print axioms outcome_DIMCID_vs_CupodBot
#print axioms outcome_DIMCID_vs_CupodTrollBot
#print axioms outcome_DIMCID_vs_JustBot
#print axioms outcome_DefectBot_vs_DefectBot
#print axioms outcome_DupocBot_vs_CooperateBot
#print axioms outcome_DupocBot_vs_DefectBot
#print axioms outcome_DupocBot_vs_OBot
#print axioms outcome_DupocBot_vs_TitForTatBot
#print axioms outcome_DupocBot_vs_CupodBot
#print axioms outcome_DupocBot_vs_MirrorBot
#print axioms outcome_DupocBot_vs_DupocBot
#print axioms outcome_EBot_vs_CooperateBot
#print axioms outcome_EBot_vs_DBot
#print axioms outcome_EBot_vs_DefectBot
#print axioms outcome_EBot_vs_EBot
#print axioms outcome_EBot_vs_MirrorBot
#print axioms outcome_EBot_vs_OBot
#print axioms outcome_EBot_vs_TitForTatBot
#print axioms outcome_GuardianBot_vs_CupodBot
#print axioms outcome_GuardianBot_vs_CupodTrollBot
#print axioms outcome_GuardianBot_vs_DBot
#print axioms outcome_GuardianBot_vs_DIMCID
#print axioms outcome_GuardianBot_vs_EBot
#print axioms outcome_GuardianBot_vs_GuardianBot
#print axioms outcome_GuardianBot_vs_OBot
#print axioms outcome_GuardianBot_vs_TitForTatBot
#print axioms outcome_GuardianBot_vs_CooperateBot
#print axioms outcome_GuardianBot_vs_DefectBot
#print axioms outcome_GuardianBot_vs_MirrorBot
#print axioms outcome_JustBot_vs_CooperateBot
#print axioms outcome_JustBot_vs_DefectBot
#print axioms outcome_JustBot_vs_OBot
#print axioms outcome_JustBot_vs_TitForTatBot
#print axioms outcome_JustBot_vs_MirrorBot
#print axioms outcome_JustBot_vs_DupocBot
#print axioms outcome_JustBot_vs_JustBot
#print axioms outcome_MirrorBot_vs_CooperateBot
#print axioms outcome_MirrorBot_vs_DBot
#print axioms outcome_MirrorBot_vs_DefectBot
#print axioms outcome_MirrorBot_vs_MirrorBot
#print axioms outcome_MirrorBot_vs_OBot
#print axioms outcome_MirrorBot_vs_TitForTatBot
#print axioms outcome_OBot_vs_CooperateBot
#print axioms outcome_OBot_vs_DBot
#print axioms outcome_OBot_vs_DefectBot
#print axioms outcome_OBot_vs_OBot
#print axioms outcome_OBot_vs_TitForTatBot
#print axioms outcome_PrudentBot_vs_CooperateBot
#print axioms outcome_PrudentBot_vs_CupodTrollBot
#print axioms outcome_PrudentBot_vs_DBot
#print axioms outcome_PrudentBot_vs_DefectBot
#print axioms outcome_PrudentBot_vs_MirrorBot
#print axioms outcome_PrudentBot_vs_OBot
#print axioms outcome_PrudentBot_vs_TitForTatBot
#print axioms outcome_TitForTatBot_vs_CooperateBot
#print axioms outcome_TitForTatBot_vs_DBot
#print axioms outcome_TitForTatBot_vs_DefectBot
#print axioms outcome_TitForTatBot_vs_TitForTatBot
#print axioms outcome_WaryBot_vs_GuardianBot
#print axioms outcome_WaryBot_vs_CooperateBot
#print axioms outcome_WaryBot_vs_CupodTrollBot
#print axioms outcome_WaryBot_vs_DBot
#print axioms outcome_WaryBot_vs_DefectBot
#print axioms outcome_WaryBot_vs_EBot
#print axioms outcome_WaryBot_vs_MirrorBot
#print axioms outcome_WaryBot_vs_TitForTatBot
#print axioms outcome_WaryBot_vs_WaryBot

-- The floors (Outcome/Floors.lean): the engine-side half of each dichotomy, on the FloorSpecA template.
#print axioms outcome_DupocBot_vs_DBot_floor
#print axioms outcome_DupocBot_vs_EBot_floor
#print axioms outcome_DupocBot_vs_CupodTrollBot_floor
#print axioms outcome_JustBot_vs_DBot_floor
#print axioms outcome_JustBot_vs_EBot_floor
#print axioms outcome_JustBot_vs_CupodTrollBot_floor
#print axioms outcome_CIMCIC_vs_CupodTrollBot_floor
#print axioms outcome_CIMCIC_vs_DBot_floor
#print axioms outcome_CIMCIC_vs_EBot_floor
#print axioms outcome_GuardianBot_vs_CIMCIC_floor
#print axioms outcome_GuardianBot_vs_DupocBot_floor
#print axioms outcome_GuardianBot_vs_JustBot_floor
#print axioms outcome_CupodBot_vs_OBot_floor
#print axioms outcome_PrudentBot_vs_DupocBot_floor
#print axioms outcome_PrudentBot_vs_PrudentBot_floor
#print axioms outcome_JustBot_vs_PrudentBot_floor
#print axioms outcome_CIMCIC_vs_PrudentBot_floor
#print axioms outcome_PrudentBot_vs_EBot_floor
#print axioms outcome_GuardianBot_vs_PrudentBot_floor
#print axioms outcome_WaryBot_vs_DupocBot_floor
#print axioms outcome_WaryBot_vs_JustBot_floor
#print axioms outcome_WaryBot_vs_PrudentBot_floor
#print axioms outcome_CupodBot_vs_PrudentBot_floor
#print axioms outcome_PrudentBot_vs_CupodBot_floor
#print axioms outcome_JustBot_vs_CupodBot_floor
#print axioms outcome_CIMCIC_vs_CupodBot_floor

-- DupocTrollBot (2026-10-13): the eleven `S'`-only cells and the one `S'`-only floor (no engine counterpart).
#print axioms outcome_DupocTrollBot_vs_CooperateBot
#print axioms outcome_DupocTrollBot_vs_CupodBot
#print axioms outcome_DupocTrollBot_vs_CupodTrollBot
#print axioms outcome_DupocTrollBot_vs_DBot
#print axioms outcome_DupocTrollBot_vs_DIMCID
#print axioms outcome_DupocTrollBot_vs_DefectBot
#print axioms outcome_DupocTrollBot_vs_DupocBot
#print axioms outcome_DupocTrollBot_vs_DupocTrollBot
#print axioms outcome_DupocTrollBot_vs_EBot
#print axioms outcome_DupocTrollBot_vs_OBot
#print axioms outcome_DupocTrollBot_vs_TitForTatBot
#print axioms outcome_DupocTrollBot_vs_CIMCIC_floor

-- DIMDID (2026-10-13, `Cells/Dimdid.lean`): the ten `S'`-only cells (three by the transposition theorem from CIMCIC's)
-- and the three `S'`-only two-hinge floors (no engine counterpart).
#print axioms outcome_DIMDID_vs_CooperateBot
#print axioms outcome_DIMDID_vs_DefectBot
#print axioms outcome_DIMDID_vs_TitForTatBot
#print axioms outcome_DIMDID_vs_DBot
#print axioms outcome_DIMDID_vs_EBot
#print axioms outcome_DIMDID_vs_CupodTrollBot
#print axioms outcome_DIMDID_vs_OBot
#print axioms outcome_DIMDID_vs_CupodBot
#print axioms outcome_DIMDID_vs_DIMCID
#print axioms outcome_DIMDID_vs_DIMDID
#print axioms outcome_DIMDID_vs_DupocBot_floor
#print axioms outcome_DIMDID_vs_CIMCIC_floor
#print axioms outcome_DIMDID_vs_PrudentBot_floor

end ArithS
