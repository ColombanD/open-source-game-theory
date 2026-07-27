import PrisonersDilemma.Bots.DBot
import PrisonersDilemma.Bots.CooperateBot
import PrisonersDilemma.Bots.DefectBot
import PrisonersDilemma.Dynamics
import PrisonersDilemma.Theorems.DefectBot
import PrisonersDilemma.Base.Helpers
import PrisonersDilemma.Theorems.DBot.Helpers

open PD.Bots
namespace PD.Theorems
theorem outcome_DBot_vs_CooperateBot (fuel : Nat):
    outcome (fuel + 3) DBot CooperateBot = some (.D, .C) := by
    have hA : play (fuel + 3) DBot CooperateBot = some .D := DBot_plays_D_against_CooperateBot (fuel)
    have hB : play (fuel + 3) CooperateBot DBot = some .C := rfl
    simp [outcome, hA, hB]

end PD.Theorems
