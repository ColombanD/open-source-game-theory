import PrisonersDilemma.Bots.EBot
import PrisonersDilemma.Bots.CooperateBot
import PrisonersDilemma.Base.Helpers
import PrisonersDilemma.Theorems.EBot.Helpers
import PrisonersDilemma.Outcome


open PD.Bots
namespace PD.Theorems
@[outcome]
theorem outcome_EBot_vs_CooperateBot :
    OutcomeSpec .nobudget 3
      (fun _ => EBot) (fun _ => CooperateBot) (some (.D, .C)) := by
    intro fuel
    have hA : play (fuel + 3) EBot CooperateBot = some .D := EBot_plays_D_against_CooperateBot (fuel)
    have hB : play (fuel + 3) CooperateBot EBot = some .C := rfl
    exact outcome_of_plays _ _ _ _ _ hA hB

end PD.Theorems
