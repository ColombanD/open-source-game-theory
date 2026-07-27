import PrisonersDilemma.Program
import PrisonersDilemma.Dynamics
import PrisonersDilemma.Bots.CooperateBot
import PrisonersDilemma.Bots.CupodBot
import PrisonersDilemma.Bots.TitForTatBot
import PrisonersDilemma.Bots.DBot
import PrisonersDilemma.Bots.OBot
import PrisonersDilemma.Bots.EBot
import PrisonersDilemma.Bots.MirrorBot
import PrisonersDilemma.Theorems.CooperateBot
import PrisonersDilemma.Theorems.DefectBot
import PrisonersDilemma.Bots.DefectBot
import PrisonersDilemma.Base.Helpers
import PrisonersDilemma.BaseTheorems
import PrisonersDilemma.Base.Asymptotics
import PrisonersDilemma.Theorems.CupodBot.Helpers

open PD
open PD.Bots
open PD.BaseTheorems
namespace PD.Theorems
/-- CupodBot vs TitForTatBot: mutual cooperation. -/
theorem outcome_CupodBot_vs_TitForTatBot (fuel : Nat):
    ∃ k, outcome (fuel + 4) (CupodBot k) TitForTatBot = some (.C, .C) := by
  let k := 0
  refine ⟨k, ?_⟩
  have hA : play (fuel + 4) (CupodBot k) TitForTatBot = some .C := by
    have hg := proofSearch_false_for_TitForTatBot k
    show eval (fuel + 4) (CupodBot k) TitForTatBot (CupodBot k) = some .C
    unfold CupodBot at hg ⊢
    simp [eval, Prog.subst, Formula.subst, hg]
  have hB : play (fuel + 4) TitForTatBot (CupodBot k) = some .C := by
    exact TitForTatBot_plays_C_against_CupodBot k fuel
  exact outcome_of_plays _ _ _ _ _ hA hB

end PD.Theorems
