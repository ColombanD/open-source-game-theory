import PrisonersDilemma.Models.DefectBot

namespace PD.Proofs.DefectBot

open PD
open PD.Action
open PD.StrategyDSL
open PD.Models.DefectBot

/-- DefectBot always returns `D` regardless of opponent source. -/
theorem action_always_defect (oppSource : SourceAST) :
    action oppSource = D := by
  simp [action, strategy, actionFor, evalActionExpr]

end PD.Proofs.DefectBot
