import PrisonersDilemma.Bots.CooperateBot
import PrisonersDilemma.Bots.DefectBot
import PrisonersDilemma.Bots.TitForTatBot
import PrisonersDilemma.Theorems.DBot
import PrisonersDilemma.Dynamics
import PrisonersDilemma.Base.Helpers
import PrisonersDilemma.Theorems.TitForTatBot.Helpers


open PD.Bots
namespace PD.Theorems
theorem outcome_TitForTatBot_vs_DefectBot (fuel : Nat):
    outcome (fuel + 3) TitForTatBot DefectBot = some (.D, .D) := by
    have hA : play (fuel + 3) TitForTatBot DefectBot = some .D := TitForTatBot_plays_D_against_DB (fuel)
    have hB : play (fuel + 3) DefectBot TitForTatBot = some .D := rfl
    simp [outcome, hA, hB]

end PD.Theorems
