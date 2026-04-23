import PrisonersDilemma.StrategyDSL
import PrisonersDilemma.Models.Bots.CooperateBot
import PrisonersDilemma.Models.Bots.DefectBot

namespace PD.Models.Bots.MirrorBot

open PD
open PD.Action
open PD.StrategyDSL


/-- Strategy definition for MirrorBot, which mimics what the opponent does against CooperateBot and DefectBot. -/
@[simp]
def strategy : ActionExpr :=
  ActionExpr.probeAndBranch CooperateBot.source C       -- Asks: What does opponent do against CooperateBot?
    (ActionExpr.actionLit C)                              -- If opponent cooperates against CooperateBot, cooperates
    (ActionExpr.probeAndBranch DefectBot.source D         -- If opponent defects against CooperateBot, ask: What does opponent do against DefectBot?
      (ActionExpr.actionLit D)                                -- If opponent defects against DefectBot, defects
      (ActionExpr.actionLit C))                               -- If opponent cooperates against DefectBot, cooperates

/-- Source encoding for MirrorBot. -/
@[simp] def source : SourceAST :=
  { tag := SourceTag.mirrorBotTag, strategy := strategy }

/-- Action chosen by MirrorBot from opponent source metadata. -/
@[simp] def action (oppSource : SourceAST) : Action :=
  evalActionExpr' strategy oppSource

end PD.Models.Bots.MirrorBot
