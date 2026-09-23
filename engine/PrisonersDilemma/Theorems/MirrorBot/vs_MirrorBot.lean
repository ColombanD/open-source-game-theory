import PrisonersDilemma.Bots.MirrorBot
import PrisonersDilemma.Base.Helpers
import PrisonersDilemma.BaseTheorems
import PrisonersDilemma.Theorems.MirrorBot.Helpers
import PrisonersDilemma.Outcome


open PD.Bots
namespace PD.Theorems
-- The library's ONLY proven no-outcome cell: `r = none` is not a special shape in the
-- template, just a different result.
@[outcome]
theorem outcome_MirrorBot_vs_MirrorBot :
    OutcomeSpec .nobudget 0
      (fun _ => MirrorBot) (fun _ => MirrorBot) none := by
    intro fuel
    simp only [Nat.add_zero]
    have hA : play fuel MirrorBot MirrorBot = none := MirrorBot_plays_none_against_MirrorBot fuel
    simp [outcome, hA]

end PD.Theorems
