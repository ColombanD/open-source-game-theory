import PrisonersDilemma.Bots.CooperateBot
import PrisonersDilemma.Bots.TitForTatBot
import PrisonersDilemma.Dynamics
import PrisonersDilemma.Base.Helpers
import PrisonersDilemma.Theorems.TitForTatBot.Helpers
import PrisonersDilemma.Outcome


open PD.Bots
namespace PD.Theorems
@[outcome]
theorem outcome_TitForTatBot_vs_CooperateBot :
    OutcomeSpec .nobudget 3
      (fun _ => TitForTatBot) (fun _ => CooperateBot) (some (.C, .C)) := by
    intro fuel
    have hA : play (fuel + 3) TitForTatBot CooperateBot = some .C := TitForTatBot_plays_C_against_CB (fuel)
    have hB : play (fuel + 3) CooperateBot TitForTatBot = some .C := rfl
    simp [outcome, hA, hB]

end PD.Theorems
