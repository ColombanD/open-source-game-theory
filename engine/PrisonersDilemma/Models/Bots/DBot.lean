import PrisonersDilemma.StrategyDSL
import PrisonersDilemma.Models.Bots.DefectBot

namespace PD.Models.Bots.DBot

open PD
open PD.Action
open PD.StrategyDSL

/-- Strategy definition for DBot.
Bot defects if the opponent cooperates against a defect probe. -/
@[simp]
def strategy (oppSource : SourceAST) : ActionExpr :=
  if probeOpponent oppSource DefectBot.source = C
    then ActionExpr.actionLit D
    else ActionExpr.actionLit C

/-- Source encoding for DBot. -/
@[simp]
def source : SourceAST :=
  { tag := SourceTag.defectTag, strategy := strategy }

/-- Action chosen by DBot from opponent source metadata. -/
@[simp]
def action (oppSource : SourceAST) : Action :=
  evalActionExpr (strategy oppSource) oppSource.tag

end PD.Models.Bots.DBot
