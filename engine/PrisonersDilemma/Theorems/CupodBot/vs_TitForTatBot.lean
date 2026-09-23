import PrisonersDilemma.Program
import PrisonersDilemma.Dynamics
import PrisonersDilemma.Bots.CupodBot
import PrisonersDilemma.Bots.TitForTatBot
import PrisonersDilemma.Base.Helpers
import PrisonersDilemma.BaseTheorems
import PrisonersDilemma.Base.Asymptotics
import PrisonersDilemma.Theorems.CupodBot.Helpers
import PrisonersDilemma.Outcome

open PD
open PD.Bots
open PD.BaseTheorems
namespace PD.Theorems
/-- CupodBot vs TitForTatBot: mutual cooperation. -/
-- Helpers take an ARBITRARY budget, so this is `.universal` — stronger than the
-- `∃ k` (at k = 0) it was stated as.
@[outcome]
theorem outcome_CupodBot_vs_TitForTatBot :
    OutcomeSpec .universal 4
      CupodBot (fun _ => TitForTatBot) (some (.C, .C)) := by
  intro k fuel
  have hA : play (fuel + 4) (CupodBot k) TitForTatBot = some .C := by
    have hg := proofSearch_false_for_TitForTatBot k
    show eval (fuel + 4) (CupodBot k) TitForTatBot (CupodBot k) = some .C
    unfold CupodBot at hg ⊢
    simp [eval, Prog.subst, Formula.subst, hg]
  have hB : play (fuel + 4) TitForTatBot (CupodBot k) = some .C := by
    exact TitForTatBot_plays_C_against_CupodBot k fuel
  exact outcome_of_plays _ _ _ _ _ hA hB

end PD.Theorems
