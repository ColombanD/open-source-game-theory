import PrisonersDilemma.Bots.DefectBot
import PrisonersDilemma.Bots.OBot
import PrisonersDilemma.Dynamics
import PrisonersDilemma.Base.Helpers
import PrisonersDilemma.Theorems.OBot.Helpers
import PrisonersDilemma.Outcome


open PD.Bots
namespace PD.Theorems
@[outcome]
theorem outcome_OBot_vs_DefectBot :
    OutcomeSpec .nobudget 3
      (fun _ => OBot) (fun _ => DefectBot) (some (.D, .D)) := by
    intro fuel
    have hA : play (fuel + 3) OBot DefectBot = some .D := OBot_plays_D_against_DB (fuel)
    have hB : play (fuel + 3) DefectBot OBot = some .D := rfl
    simp [outcome, hA, hB]

end PD.Theorems
