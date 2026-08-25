import PrisonersDilemma.Bots.MirrorBot
import PrisonersDilemma.Bots.DBot
import PrisonersDilemma.Base.Helpers
import PrisonersDilemma.BaseTheorems
import PrisonersDilemma.Theorems.MirrorBot.Helpers
import PrisonersDilemma.Outcome


open PD.Bots
namespace PD.Theorems
@[outcome]
theorem outcome_MirrorBot_vs_DBot :
    OutcomeSpec .nobudget 6
      (fun _ => MirrorBot) (fun _ => DBot) (some (.C, .C)) := by
    intro fuel
    have hA : play (fuel + 6) MirrorBot DBot = some .C := MirrorBot_plays_C_against_DBot (fuel)
    have hB : play (fuel + 6) DBot MirrorBot = some .C := DBot_plays_C_against_MirrorBot (fuel + 1)
    simp [outcome, hA, hB]

end PD.Theorems
