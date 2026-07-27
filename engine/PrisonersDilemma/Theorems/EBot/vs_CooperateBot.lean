import PrisonersDilemma.Bots.EBot
import PrisonersDilemma.Bots.CooperateBot
import PrisonersDilemma.Base.Helpers
import PrisonersDilemma.Theorems.EBot.Helpers


open PD.Bots
namespace PD.Theorems
theorem outcome_EBot_vs_CooperateBot (fuel : Nat):
    outcome (fuel + 3) EBot CooperateBot = some (.D, .C) := by
    have hA : play (fuel + 3) EBot CooperateBot = some .D := EBot_plays_D_against_CooperateBot (fuel)
    have hB : play (fuel + 3) CooperateBot EBot = some .C := rfl
    exact outcome_of_plays _ _ _ _ _ hA hB

end PD.Theorems
