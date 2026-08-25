import PrisonersDilemma.Program
import PrisonersDilemma.Dynamics
import PrisonersDilemma.Bots.CooperateBot
import PrisonersDilemma.Theorems.CooperateBot.Helpers
import PrisonersDilemma.Outcome

open PD
open PD.Bots

namespace PD.Theorems
-- CooperateBot vs itself: mutual cooperation, (C, C).
@[outcome]
theorem outcome_CooperateBot_vs_CooperateBot :
    OutcomeSpec .nobudget 1
      (fun _ => CooperateBot) (fun _ => CooperateBot) (some (.C, .C)) := by
  intro n
  unfold outcome
  rw [play_CooperateBot]
  rfl

end PD.Theorems
