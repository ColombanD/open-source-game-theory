import PrisonersDilemma.Bots.EBot
import PrisonersDilemma.Bots.OBot
import PrisonersDilemma.Bots.CooperateBot
import PrisonersDilemma.Bots.DefectBot
import PrisonersDilemma.Bots.DBot
import PrisonersDilemma.Base.Helpers
import PrisonersDilemma.Theorems.DBot
import PrisonersDilemma.Theorems.OBot
import PrisonersDilemma.Theorems.TitForTatBot
import PrisonersDilemma.Theorems.MirrorBot
import PrisonersDilemma.Theorems.EBot.Helpers


open PD.Bots
namespace PD.Theorems
theorem outcome_EBot_vs_DefectBot (fuel : Nat):
    outcome (fuel + 5) EBot DefectBot = some (.D, .D) := by
    have hA : play (fuel + 5) EBot DefectBot = some .D := EBot_plays_D_against_DefectBot (fuel)
    have hB : play (fuel + 5) DefectBot EBot = some .D := rfl
    exact outcome_of_plays _ _ _ _ _ hA hB

end PD.Theorems
