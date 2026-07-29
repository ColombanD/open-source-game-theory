import PrisonersDilemma.Program
import PrisonersDilemma.Dynamics
import PrisonersDilemma.Bots.LlmGenerations.WaryBot
import PrisonersDilemma.Bots.CupodTrollBot
import PrisonersDilemma.Theorems.CupodTrollBot.Helpers
import PrisonersDilemma.Base.Helpers
import PrisonersDilemma.BaseTheorems
import PrisonersDilemma.Theorems.WaryBot.Helpers

open PD
open PD.BaseTheorems
open PD.Bots
namespace PD.Theorems

/-- The troll's structural-identity guard fails at EVERY budget: WaryBot's
    guard formula is a `.neg`, CupodBot's a `.plays`, so the sources differ. -/
theorem CupodTrollBot_plays_C_against_WaryBot (k fuel : Nat) :
    play (fuel + 2) (CupodTrollBot k) (WaryBot k) = some .C :=
  CupodTrollBot_cooperates_if_opp_not_CupodBot k fuel (WaryBot k)
    (by simp [WaryBot, CupodBot])

/-- WaryBot cannot refute the troll's (semantically true) cooperation. -/
theorem proofSearch_false_wary_CupodTrollBot (k : Nat) :
    proofSearch k (.neg (.plays (CupodTrollBot k) (WaryBot k) .C)) = false := by
  cases h : proofSearch k (.neg (.plays (CupodTrollBot k) (WaryBot k) .C)) with
  | true =>
      have hI : (Formula.plays (CupodTrollBot k) (WaryBot k) .C).interp := by
        unfold Formula.interp
        exact ⟨2, CupodTrollBot_plays_C_against_WaryBot k 0⟩
      exact absurd hI (proofSearch_sound _ _ h)
  | false => rfl

/-- WaryBot vs CupodTrollBot: mutual cooperation at EVERY budget — the troll's
    identity guard fails structurally, and its cooperation is irrefutable.
    A soundness-only cell, fully general in `k`. -/
theorem outcome_WaryBot_vs_CupodTrollBot (k fuel : Nat) :
    outcome (fuel + 2) (WaryBot k) (CupodTrollBot k) = some (.C, .C) := by
  have hg := proofSearch_false_wary_CupodTrollBot k
  have hA : play (fuel + 2) (WaryBot k) (CupodTrollBot k) = some .C := by
    show eval (fuel + 2) (WaryBot k) (CupodTrollBot k) (WaryBot k) = some .C
    unfold WaryBot at hg ⊢
    simp [eval, Prog.subst, Formula.subst, hg]
  exact outcome_of_plays _ _ _ _ _ hA
    (CupodTrollBot_plays_C_against_WaryBot k fuel)
end PD.Theorems
