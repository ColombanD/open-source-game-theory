import PrisonersDilemma.Bots.DBot
import PrisonersDilemma.Bots.CooperateBot
import PrisonersDilemma.Dynamics
import PrisonersDilemma.Base.Helpers
import PrisonersDilemma.Theorems.DBot.Helpers
import PrisonersDilemma.Outcome

open PD.Bots
namespace PD.Theorems
@[outcome]
theorem outcome_DBot_vs_CooperateBot :
    OutcomeSpec .nobudget 3
      (fun _ => DBot) (fun _ => CooperateBot) (some (.D, .C)) := by
    intro fuel
    have hA : play (fuel + 3) DBot CooperateBot = some .D := DBot_plays_D_against_CooperateBot (fuel)
    have hB : play (fuel + 3) CooperateBot DBot = some .C := rfl
    simp [outcome, hA, hB]

end PD.Theorems
