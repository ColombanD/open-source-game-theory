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
theorem outcome_MirrorBot_vs_MirrorBot (fuel : Nat):
    outcome fuel MirrorBot MirrorBot = none := by
    have hA : play fuel MirrorBot MirrorBot = none := MirrorBot_plays_none_against_MirrorBot fuel
    simp [outcome, hA]

end PD.Theorems
