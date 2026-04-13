import PrisonersDilemma.Models.Bots.DefectBot

namespace PD.Proofs.DefectBot

open PD
open PD.Action
open PD.StrategyDSL
open PD.Models.Bots.DefectBot

/-- DefectBot always returns `D` regardless of opponent source. -/
theorem action_always_defect (oppSource : SourceAST) :
    action oppSource = D := by
  unfold action strategy evalActionExpr' evalActionExpr
  simp

end PD.Proofs.DefectBot
