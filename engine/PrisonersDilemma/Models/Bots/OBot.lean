import PrisonersDilemma.StrategyDSL
import PrisonersDilemma.Models.Bots.CooperateBot
import PrisonersDilemma.Models.Bots.DefectBot

namespace PD.Models.Bots.OBot

open PD
open PD.Action
open PD.StrategyDSL

/-- Strategy definition for OBot. -/
@[simp]
def strategy : ActionExpr :=
  ActionExpr.probeAndBranch CooperateBot.source C       -- Asks: What does opponent do against CooperateBot?
    (ActionExpr.probeAndBranch DefectBot.source C           -- If opponent cooperates against CooperateBot, ask: What does opponent do against DefectBot?
      (ActionExpr.actionLit C)                                  -- If opponent cooperates against DefectBot, cooperate
      (ActionExpr.actionLit D))                                 -- If opponent defects against DefectBot, defect
    (ActionExpr.probeAndBranch DefectBot.source D           -- If opponent defects against CooperateBot, ask: What does opponent do against DefectBot?
      (ActionExpr.probeAndBranch CooperateBot.source C          -- If opponent defects against DefectBot, ask: What does opponent do against CooperateBot?
        (ActionExpr.actionLit C)                                    -- If opponent cooperates against CooperateBot, cooperate
        (ActionExpr.actionLit D))                                   -- If opponent defects against CooperateBot, defect
      (ActionExpr.actionLit D))                                 -- If opponent cooperates against DefectBot, defect

/-- Source encoding for OBot. -/
@[simp] def source : SourceAST :=
  { tag := SourceTag.oBotTag, strategy := strategy }

/-- Action chosen by OBot from opponent source metadata. -/
@[simp] def action (oppSource : SourceAST) : Action :=
  evalActionExpr' strategy oppSource

end PD.Models.Bots.OBot
