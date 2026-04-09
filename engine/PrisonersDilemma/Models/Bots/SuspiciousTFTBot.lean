import PrisonersDilemma.StrategyDSL

namespace PD.Models.Bots.SuspiciousTFTBot

open PD
open PD.Action
open PD.StrategyDSL

/-- Strategy definition for SuspiciousTFTBot. -/
@[simp]
def strategy : ActionExpr := OpenSourceStrategyDSL.defectStrategy

/-- Source encoding for SuspiciousTFTBot. -/
@[simp]
def source : SourceAST :=
  { tag := SourceTag.suspiciousTFTTag, strategy := strategy }

/-- Action chosen by SuspiciousTFTBot from opponent source metadata. -/
@[simp]
def action (oppSource : SourceAST) : Action :=
  evalActionExpr strategy oppSource.tag

end PD.Models.Bots.SuspiciousTFTBot
