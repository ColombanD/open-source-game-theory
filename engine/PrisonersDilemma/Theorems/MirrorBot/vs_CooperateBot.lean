import PrisonersDilemma.Bots.MirrorBot
import PrisonersDilemma.Bots.CooperateBot
import PrisonersDilemma.Base.Helpers
import PrisonersDilemma.BaseTheorems
import PrisonersDilemma.Theorems.MirrorBot.Helpers


open PD.Bots
namespace PD.Theorems
theorem outcome_MirrorBot_vs_CooperateBot (fuel : Nat):
    outcome (fuel + 3) MirrorBot CooperateBot = some (.C, .C) := by
    have hA : play (fuel + 3) MirrorBot CooperateBot = some .C := MirrorBot_plays_C_against_CooperateBot (fuel)
    have hB : play (fuel + 3) CooperateBot MirrorBot = some .C := rfl
    simp only [outcome, hA, hB, Option.bind_eq_bind, Option.bind_some]

end PD.Theorems
