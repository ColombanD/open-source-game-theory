import PrisonersDilemma.Bots.MirrorBot
import PrisonersDilemma.Bots.OBot
import PrisonersDilemma.Base.Helpers
import PrisonersDilemma.BaseTheorems
import PrisonersDilemma.Theorems.MirrorBot.Helpers
import PrisonersDilemma.Outcome


open PD.Bots
namespace PD.Theorems
@[outcome]
theorem outcome_MirrorBot_vs_OBot :
    OutcomeSpec .nobudget 7
      (fun _ => MirrorBot) (fun _ => OBot) (some (.D, .D)) := by
    intro fuel
    have hA : play (fuel + 7) MirrorBot OBot = some .D := MirrorBot_plays_D_against_OBot (fuel)
    have hB : play (fuel + 7) OBot MirrorBot = some .D := OBot_plays_D_against_MirrorBot (fuel + 1)
    simp [outcome, hA, hB]

end PD.Theorems
