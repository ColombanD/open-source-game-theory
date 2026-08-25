import PrisonersDilemma.Bots.MirrorBot
import PrisonersDilemma.Bots.DefectBot
import PrisonersDilemma.Base.Helpers
import PrisonersDilemma.BaseTheorems
import PrisonersDilemma.Theorems.MirrorBot.Helpers
import PrisonersDilemma.Outcome


open PD.Bots
namespace PD.Theorems
@[outcome]
theorem outcome_MirrorBot_vs_DefectBot :
    OutcomeSpec .nobudget 3
      (fun _ => MirrorBot) (fun _ => DefectBot) (some (.D, .D)) := by
    intro fuel
    have hA : play (fuel + 3) MirrorBot DefectBot = some .D := MirrorBot_plays_D_against_DefectBot (fuel)
    have hB : play (fuel + 3) DefectBot MirrorBot = some .D := rfl
    simp [outcome, hA, hB]

end PD.Theorems
