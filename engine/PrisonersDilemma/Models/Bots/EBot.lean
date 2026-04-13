import PrisonersDilemma.StrategyDSL
import PrisonersDilemma.Models.Bots.CooperateBot
import PrisonersDilemma.Models.Bots.DefectBot
import PrisonersDilemma.Models.Bots.MirrorBot

namespace PD.Models.Bots.EBot

open PD
open PD.Action
open PD.StrategyDSL

/-- Strategy definition for EBot. -/
@[simp]
def strategy : ActionExpr :=
  ActionExpr.probeAndBranch DefectBot.source C
    (ActionExpr.actionLit D)
    (ActionExpr.probeAndBranch CooperateBot.source C
      (ActionExpr.actionLit C)
      (ActionExpr.probeAndBranch MirrorBot.source C
        (ActionExpr.actionLit C)
        (ActionExpr.actionLit D)))


/-- Source encoding for EBot. -/
@[simp] def source : SourceAST :=
  { tag := SourceTag.eBotTag, strategy := strategy }

/-- Action chosen by EBot from opponent source metadata. -/
@[simp] def action (oppSource : SourceAST) : Action :=
  evalActionExpr' strategy oppSource

end PD.Models.Bots.EBot
