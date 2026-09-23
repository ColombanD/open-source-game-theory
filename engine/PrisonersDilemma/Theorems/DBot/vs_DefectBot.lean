import PrisonersDilemma.Bots.DBot
import PrisonersDilemma.Bots.DefectBot
import PrisonersDilemma.Dynamics
import PrisonersDilemma.Theorems.DefectBot.Helpers
import PrisonersDilemma.Base.Helpers
import PrisonersDilemma.Theorems.DBot.Helpers
import PrisonersDilemma.Outcome

open PD.Bots
namespace PD.Theorems
@[outcome]
theorem outcome_DBot_vs_DefectBot :
    OutcomeSpec .nobudget 3
      (fun _ => DBot) (fun _ => DefectBot) (some (.C, .D)) := by
    intro fuel
    have hA : play (fuel + 3) DBot DefectBot = some .C := DBot_plays_C_against_DefectBot (fuel)
    have hB : play (fuel + 3) DefectBot DBot = some .D := rfl
    simp [outcome, hA, hB]

end PD.Theorems
