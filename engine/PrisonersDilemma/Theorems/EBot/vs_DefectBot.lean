import PrisonersDilemma.Bots.EBot
import PrisonersDilemma.Bots.DefectBot
import PrisonersDilemma.Base.Helpers
import PrisonersDilemma.Theorems.EBot.Helpers
import PrisonersDilemma.Outcome


open PD.Bots
namespace PD.Theorems
@[outcome]
theorem outcome_EBot_vs_DefectBot :
    OutcomeSpec .nobudget 5
      (fun _ => EBot) (fun _ => DefectBot) (some (.D, .D)) := by
    intro fuel
    have hA : play (fuel + 5) EBot DefectBot = some .D := EBot_plays_D_against_DefectBot (fuel)
    have hB : play (fuel + 5) DefectBot EBot = some .D := rfl
    exact outcome_of_plays _ _ _ _ _ hA hB

end PD.Theorems
