import ArithS.Outcome.Spec
import ArithS.Cells.RedCellEngine
import ArithS.Outcome.Matrix.CIMCIC
import ArithS.Outcome.Matrix.CooperateBot
import ArithS.Outcome.Matrix.CupodBot
import ArithS.Outcome.Matrix.CupodTrollBot
import ArithS.Outcome.Matrix.DBot
import ArithS.Outcome.Matrix.DIMCID
import ArithS.Outcome.Matrix.DefectBot
import ArithS.Outcome.Matrix.DupocBot
import ArithS.Outcome.Matrix.EBot
import ArithS.Outcome.Matrix.GuardianBot
import ArithS.Outcome.Matrix.JustBot
import ArithS.Outcome.Matrix.MirrorBot
import ArithS.Outcome.Matrix.OBot
import ArithS.Outcome.Matrix.PrudentBot
import ArithS.Outcome.Matrix.TitForTatBot
import ArithS.Outcome.Matrix.WaryBot

/-!
# ArithS.Audit.Outcome — the census of the outcome layer

Every cell of `Outcome/Matrix/*.lean` (the engine-shaped statements) and the engine-level red cell.
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
#print axioms outcome_CIMCIC_vs_Dupoc
#print axioms outcome_CIMCIC_vs_Just7
#print axioms outcome_CooperateBot_vs_CooperateBot
#print axioms outcome_CooperateBot_vs_DefectBot
#print axioms outcome_CupodBot_vs_CooperateBot
#print axioms outcome_CupodBot_vs_DBot
#print axioms outcome_CupodBot_vs_DefectBot
#print axioms outcome_CupodBot_vs_EBot
#print axioms outcome_CupodBot_vs_TitForTatBot
#print axioms outcome_Cupod_vs_MirrorBot
#print axioms outcome_Cupod_vs_Cupod
#print axioms outcome_CupodTrollBot_vs_CooperateBot
#print axioms outcome_CupodTroll7_vs_CupodBot
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
#print axioms outcome_DIMCID_vs_Cupod
#print axioms outcome_DIMCID_vs_CupodTroll7
#print axioms outcome_DIMCID_vs_Just7
#print axioms outcome_DefectBot_vs_DefectBot
#print axioms outcome_DupocBot_vs_CooperateBot
#print axioms outcome_DupocBot_vs_DefectBot
#print axioms outcome_DupocBot_vs_OBot
#print axioms outcome_DupocBot_vs_TitForTatBot
#print axioms outcome_DupocBot_vs_CupodBot
#print axioms outcome_Dupoc_vs_MirrorBot
#print axioms outcome_Dupoc_vs_Dupoc
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
#print axioms outcome_Just_vs_MirrorBot
#print axioms outcome_Just7_vs_Dupoc
#print axioms outcome_Just7_vs_Just7
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

end ArithS
