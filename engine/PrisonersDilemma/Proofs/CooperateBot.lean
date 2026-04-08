import PrisonersDilemma.Models.CooperateBot

namespace PD.Proofs.CooperateBot

open PD
open PD.Action
open PD.StrategyDSL
open PD.Models.CooperateBot

/-- CooperateBot always returns `C` regardless of opponent source. -/
theorem action_always_cooperate (oppSource : SourceAST) :
    action oppSource = C := by
  simp [action, strategy, actionFor, evalActionExpr]

end PD.Proofs.CooperateBot
