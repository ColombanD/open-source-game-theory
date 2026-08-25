import PrisonersDilemma.Bots.DefectBot
import PrisonersDilemma.Bots.TitForTatBot
import PrisonersDilemma.Dynamics
import PrisonersDilemma.Base.Helpers
import PrisonersDilemma.Theorems.TitForTatBot.Helpers
import PrisonersDilemma.Outcome


open PD.Bots
namespace PD.Theorems
@[outcome]
theorem outcome_TitForTatBot_vs_DefectBot :
    OutcomeSpec .nobudget 3
      (fun _ => TitForTatBot) (fun _ => DefectBot) (some (.D, .D)) := by
    intro fuel
    have hA : play (fuel + 3) TitForTatBot DefectBot = some .D := TitForTatBot_plays_D_against_DB (fuel)
    have hB : play (fuel + 3) DefectBot TitForTatBot = some .D := rfl
    simp [outcome, hA, hB]

end PD.Theorems
