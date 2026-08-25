import PrisonersDilemma.Program
import PrisonersDilemma.Dynamics
import PrisonersDilemma.Bots.CooperateBot
import PrisonersDilemma.Bots.DefectBot
import PrisonersDilemma.Theorems.DefectBot.Helpers
import PrisonersDilemma.Theorems.CooperateBot.Helpers
import PrisonersDilemma.Outcome

open PD
open PD.Bots

namespace PD.Theorems
-- CooperateBot vs DefectBot: the cooperator is exploited, (C, D).
@[outcome]
theorem outcome_CooperateBot_vs_DefectBot :
    OutcomeSpec .nobudget 1
      (fun _ => CooperateBot) (fun _ => DefectBot) (some (.C, .D)) := by
  intro n
  unfold outcome
  rw [play_CooperateBot, play_DefectBot]
  rfl

end PD.Theorems
