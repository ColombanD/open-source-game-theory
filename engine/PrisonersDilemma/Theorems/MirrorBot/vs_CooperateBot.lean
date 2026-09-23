import PrisonersDilemma.Bots.MirrorBot
import PrisonersDilemma.Bots.CooperateBot
import PrisonersDilemma.Base.Helpers
import PrisonersDilemma.BaseTheorems
import PrisonersDilemma.Theorems.MirrorBot.Helpers
import PrisonersDilemma.Outcome


open PD.Bots
namespace PD.Theorems
@[outcome]
theorem outcome_MirrorBot_vs_CooperateBot :
    OutcomeSpec .nobudget 3
      (fun _ => MirrorBot) (fun _ => CooperateBot) (some (.C, .C)) := by
    intro fuel
    have hA : play (fuel + 3) MirrorBot CooperateBot = some .C := MirrorBot_plays_C_against_CooperateBot (fuel)
    have hB : play (fuel + 3) CooperateBot MirrorBot = some .C := rfl
    simp only [outcome, hA, hB, Option.bind_eq_bind, Option.bind_some]

end PD.Theorems
