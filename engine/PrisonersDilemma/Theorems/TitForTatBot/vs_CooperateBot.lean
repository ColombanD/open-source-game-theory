import PrisonersDilemma.Bots.CooperateBot
import PrisonersDilemma.Bots.DefectBot
import PrisonersDilemma.Bots.TitForTatBot
import PrisonersDilemma.Theorems.DBot.Helpers
import PrisonersDilemma.Theorems.DBot.vs_CooperateBot
import PrisonersDilemma.Theorems.DBot.vs_DBot
import PrisonersDilemma.Theorems.DBot.vs_DefectBot
import PrisonersDilemma.Dynamics
import PrisonersDilemma.Base.Helpers
import PrisonersDilemma.Theorems.TitForTatBot.Helpers


open PD.Bots
namespace PD.Theorems
theorem outcome_TitForTatBot_vs_CooperateBot (fuel : Nat):
    outcome (fuel + 3) TitForTatBot CooperateBot = some (.C, .C) := by
    have hA : play (fuel + 3) TitForTatBot CooperateBot = some .C := TitForTatBot_plays_C_against_CB (fuel)
    have hB : play (fuel + 3) CooperateBot TitForTatBot = some .C := rfl
    simp [outcome, hA, hB]

end PD.Theorems
