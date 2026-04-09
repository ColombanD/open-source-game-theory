import PrisonersDilemma.StrategyDSL

namespace PD.Models.Bots.TitForTatBot

open PD
open PD.Action
open PD.StrategyDSL
open PD.Models.Bots

/-- Strategy definition for TitForTatBot.
Bot cooperates if the opponent cooperates against a cooperate probe. -/
@[simp]
def strategy (oppSource : SourceAST) : ActionExpr :=
  if probeOpponent oppSource CooperateBot.source = C
    then ActionExpr.actionLit C
    else ActionExpr.actionLit D

/-- Source encoding for TitForTatBot. -/
@[simp]
def source : SourceAST :=
  { tag := SourceTag.titForTatTag, strategy := strategy }

/-- Action chosen by TitForTatBot from opponent source metadata. -/
@[simp]
def action (oppSource : SourceAST) : Action :=
  evalActionExpr (strategy oppSource) oppSource.tag

end PD.Models.Bots.TitForTatBot
