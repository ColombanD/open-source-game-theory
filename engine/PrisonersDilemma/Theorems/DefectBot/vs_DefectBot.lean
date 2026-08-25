import PrisonersDilemma.Program
import PrisonersDilemma.Dynamics
import PrisonersDilemma.Bots.DefectBot
import PrisonersDilemma.Theorems.DefectBot.Helpers
import PrisonersDilemma.Outcome

open PD
open PD.Bots

namespace PD.Theorems
-- DefectBot vs itself: mutual defection, (D, D).
@[outcome]
theorem outcome_DefectBot_vs_DefectBot :
    OutcomeSpec .nobudget 1
      (fun _ => DefectBot) (fun _ => DefectBot) (some (.D, .D)) := by
  intro n
  unfold outcome
  rw [play_DefectBot]
  rfl

end PD.Theorems
