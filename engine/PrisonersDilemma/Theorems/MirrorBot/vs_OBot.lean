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
theorem outcome_MirrorBot_vs_OBot (fuel : Nat):
    outcome (fuel + 7) MirrorBot OBot = some (.D, .D) := by
    have hA : play (fuel + 7) MirrorBot OBot = some .D := MirrorBot_plays_D_against_OBot (fuel)
    have hB : play (fuel + 7) OBot MirrorBot = some .D := OBot_plays_D_against_MirrorBot (fuel + 1)
    simp [outcome, hA, hB]

end PD.Theorems
