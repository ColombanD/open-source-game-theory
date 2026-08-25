import PrisonersDilemma.Bots.CooperateBot
import PrisonersDilemma.Bots.OBot
import PrisonersDilemma.Dynamics
import PrisonersDilemma.Base.Helpers
import PrisonersDilemma.Theorems.OBot.Helpers
import PrisonersDilemma.Outcome


open PD.Bots
namespace PD.Theorems
@[outcome]
theorem outcome_OBot_vs_CooperateBot :
    OutcomeSpec .nobudget 5
      (fun _ => OBot) (fun _ => CooperateBot) (some (.C, .C)) := by
    intro fuel
    have hA : play (fuel + 5) OBot CooperateBot = some .C := OBot_plays_C_against_CB (fuel)
    have hB : play (fuel + 5) CooperateBot OBot = some .C := rfl
    simp [outcome, hA, hB]

end PD.Theorems
