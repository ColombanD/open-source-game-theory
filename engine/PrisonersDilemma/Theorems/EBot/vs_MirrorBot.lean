import PrisonersDilemma.Bots.EBot
import PrisonersDilemma.Base.Helpers
import PrisonersDilemma.Theorems.MirrorBot.Helpers
import PrisonersDilemma.Theorems.EBot.Helpers


open PD.Bots
namespace PD.Theorems
theorem outcome_EBot_vs_MirrorBot (fuel : Nat):
    outcome (fuel + 8) EBot MirrorBot = some (.C, .C) := by
    have hA : play (fuel + 8) EBot MirrorBot = some .C := EBot_plays_C_against_MirrorBot (fuel + 1)
    have hB : play (fuel + 8) MirrorBot EBot = some .C := by
        have hEBotPlays : play (fuel + 7) EBot MirrorBot = some .C :=
            EBot_plays_C_against_MirrorBot fuel
        show eval (fuel + 7) EBot MirrorBot EBot = some .C
        exact hEBotPlays
    exact outcome_of_plays _ _ _ _ _ hA hB

end PD.Theorems
