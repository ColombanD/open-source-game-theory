import PrisonersDilemma.Models.Bots.CupodBot

namespace PD.Proofs.CupodBot

open PD
open PD.Action
open PD.StrategyDSL

/-- CUPOD's source always has the cupodTag identifier. -/
theorem cupodBot_source_tag : PD.Models.Bots.CupodBot.source.tag = SourceTag.cupodTag := by
  simp [PD.Models.Bots.CupodBot.source]

/-- CUPOD's strategy is the strategy field of its source. -/
theorem cupodBot_strategy_eq :
  PD.Models.Bots.CupodBot.strategy = PD.Models.Bots.CupodBot.source.strategy := by
  rfl

end PD.Proofs.CupodBot
