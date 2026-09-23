import PrisonersDilemma.Bots.MirrorBot
import PrisonersDilemma.Bots.TitForTatBot
import PrisonersDilemma.Base.Helpers
import PrisonersDilemma.BaseTheorems
import PrisonersDilemma.Theorems.MirrorBot.Helpers
import PrisonersDilemma.Outcome


open PD.Bots
namespace PD.Theorems
@[outcome]
theorem outcome_MirrorBot_vs_TitForTatBot :
    OutcomeSpec .nobudget 6
      (fun _ => MirrorBot) (fun _ => TitForTatBot) (some (.C, .C)) := by
    intro fuel
    have hA : play (fuel + 6) MirrorBot TitForTatBot = some .C := MirrorBot_plays_C_against_TitForTatBot (fuel)
    have hB : play (fuel + 6) TitForTatBot MirrorBot = some .C := TitForTatBot_plays_C_against_MirrorBot (fuel + 1)
    simp [outcome, hA, hB]

end PD.Theorems
