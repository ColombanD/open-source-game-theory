import PrisonersDilemma.StrategyDSL
import PrisonersDilemma.Models.Bots.CooperateBot

namespace PD.Models.Bots.TitForTatBot

open PD
open PD.Action
open PD.StrategyDSL
open PD.Models.Bots

/-- Strategy definition for TitForTatBot.
Bot cooperates if the opponent cooperates against a cooperate probe. -/
@[simp]
def strategy : ActionExpr :=
  ActionExpr.probeAndBranch CooperateBot.source C
    (ActionExpr.actionLit C)  -- If opponent cooperates against CooperateBot, cooperate
    (ActionExpr.actionLit D)  -- Otherwise, defect

/-- Source encoding for TitForTatBot. -/
@[simp]
def source : SourceAST :=
  { tag := SourceTag.titForTatTag, strategy := strategy }

/-- Action chosen by TitForTatBot from opponent source metadata. -/
@[simp]
def action (oppSource : SourceAST) : Action :=
  evalActionExpr' strategy oppSource

end PD.Models.Bots.TitForTatBot
