import PrisonersDilemma.StrategyDSL

namespace PD.Models.Bots.DBot

open PD
open PD.Action
open PD.StrategyDSL
open PD.Models.Bots.DefectBot

/-- Strategy definition for DBot.
Bot defects if the opponent cooperates against a defect probe. -/
@[simp]
def strategy (oppSource : SourceAST) : Action :=
  if probeOpponent oppSource defectBotSource = C then D else C

/-- Source encoding for DBot. -/
@[simp]
def source : SourceAST :=
  { tag := SourceTag.defectTag, strategy := ActionExpr.actionLit C }

/-- Action chosen by DBot from opponent source metadata. -/
@[simp]
def action (oppSource : SourceAST) : Action :=
  strategy oppSource

end PD.Models.Bots.DBot
