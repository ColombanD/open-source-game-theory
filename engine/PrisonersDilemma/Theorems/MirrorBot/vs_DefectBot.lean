import PrisonersDilemma.Bots.MirrorBot
import PrisonersDilemma.Bots.DefectBot
import PrisonersDilemma.Base.Helpers
import PrisonersDilemma.BaseTheorems
import PrisonersDilemma.Theorems.MirrorBot.Helpers


open PD.Bots
namespace PD.Theorems
theorem outcome_MirrorBot_vs_DefectBot (fuel : Nat):
    outcome (fuel + 3) MirrorBot DefectBot = some (.D, .D) := by
    have hA : play (fuel + 3) MirrorBot DefectBot = some .D := MirrorBot_plays_D_against_DefectBot (fuel)
    have hB : play (fuel + 3) DefectBot MirrorBot = some .D := rfl
    simp [outcome, hA, hB]

end PD.Theorems
