import PrisonersDilemma.Bots.CooperateBot
import PrisonersDilemma.Bots.DefectBot
import PrisonersDilemma.Bots.TitForTatBot
import PrisonersDilemma.Bots.OBot
import PrisonersDilemma.Theorems.DBot
import PrisonersDilemma.Theorems.TitForTatBot
import PrisonersDilemma.Dynamics
import PrisonersDilemma.Base.Helpers
import PrisonersDilemma.Theorems.OBot.Helpers


open PD.Bots
namespace PD.Theorems
theorem outcome_OBot_vs_DefectBot (fuel : Nat):
    outcome (fuel + 3) OBot DefectBot = some (.D, .D) := by
    have hA : play (fuel + 3) OBot DefectBot = some .D := OBot_plays_D_against_DB (fuel)
    have hB : play (fuel + 3) DefectBot OBot = some .D := rfl
    simp [outcome, hA, hB]

end PD.Theorems
