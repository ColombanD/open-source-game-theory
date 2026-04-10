import PrisonersDilemma.StrategyDSL
import PrisonersDilemma.Models.Bots.DefectBot

namespace PD.Models.Bots.DBot

open PD
open PD.Action
open PD.StrategyDSL

/-- Strategy definition for DBot.
Bot defects if the opponent cooperates against a defect probe. -/
@[simp]
def strategy : ActionExpr :=
  ActionExpr.probeAndBranch DefectBot.source C
    (ActionExpr.actionLit D)  -- If opponent cooperates against DefectBot, defect
    (ActionExpr.actionLit C)  -- Otherwise, cooperate

/-- Source encoding for DBot. -/
@[simp]
def source : SourceAST :=
  { tag := SourceTag.dBotTag, strategy := strategy }

/-- Action chosen by DBot from opponent source metadata. -/
@[simp]
def action (oppSource : SourceAST) : Action :=
  evalActionExpr' strategy oppSource

end PD.Models.Bots.DBot
