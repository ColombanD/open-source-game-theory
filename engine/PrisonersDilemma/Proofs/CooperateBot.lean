import PrisonersDilemma.Models.Bots.CooperateBot

namespace PD.Proofs.CooperateBot

open PD
open PD.Action
open PD.StrategyDSL
open PD.Models.Bots.CooperateBot

/-- CooperateBot always returns `C` regardless of opponent source. -/
theorem action_always_cooperate (oppSource : SourceAST) :
    action oppSource = C := by
  unfold action strategy evalActionExpr' evalActionExpr
  simp

end PD.Proofs.CooperateBot
