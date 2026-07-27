import PrisonersDilemma.Bots.MirrorBot
import PrisonersDilemma.Bots.CooperateBot
import PrisonersDilemma.Bots.DefectBot
import PrisonersDilemma.Bots.DBot
import PrisonersDilemma.Bots.TitForTatBot
import PrisonersDilemma.Bots.OBot
import PrisonersDilemma.Base.Helpers
import PrisonersDilemma.BaseTheorems
import PrisonersDilemma.Theorems.MirrorBot.Helpers


open PD.Bots
namespace PD.Theorems
theorem outcome_MirrorBot_vs_TitForTatBot (fuel : Nat):
    outcome (fuel + 6) MirrorBot TitForTatBot = some (.C, .C) := by
    have hA : play (fuel + 6) MirrorBot TitForTatBot = some .C := MirrorBot_plays_C_against_TitForTatBot (fuel)
    have hB : play (fuel + 6) TitForTatBot MirrorBot = some .C := TitForTatBot_plays_C_against_MirrorBot (fuel + 1)
    simp [outcome, hA, hB]

end PD.Theorems
