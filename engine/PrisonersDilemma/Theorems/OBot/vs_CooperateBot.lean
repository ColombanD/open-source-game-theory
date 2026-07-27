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
theorem outcome_OBot_vs_CooperateBot (fuel : Nat):
    outcome (fuel + 5) OBot CooperateBot = some (.C, .C) := by
    have hA : play (fuel + 5) OBot CooperateBot = some .C := OBot_plays_C_against_CB (fuel)
    have hB : play (fuel + 5) CooperateBot OBot = some .C := rfl
    simp [outcome, hA, hB]

end PD.Theorems
