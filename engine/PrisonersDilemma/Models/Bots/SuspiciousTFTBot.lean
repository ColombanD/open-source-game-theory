import PrisonersDilemma.Models.OpenSourceStrategyDSL

namespace PD.Models.Bots.SuspiciousTFTBot

open PD
open PD.Action
open PD.Models.OpenSourceStrategyDSL

/-- Suspicious TitForTat in one-shot open-source PD is encoded as always defect. -/
@[simp]
def strategy : ActionExpr := OpenSourceStrategyDSL.defectStrategy

@[simp]
def source : SourceAST :=
  { tag := SourceTag.suspiciousTFTTag, strategy := strategy }

@[simp]
def action (oppSource : SourceAST) : Action :=
  evalActionExpr strategy oppSource.tag

end PD.Models.Bots.SuspiciousTFTBot
