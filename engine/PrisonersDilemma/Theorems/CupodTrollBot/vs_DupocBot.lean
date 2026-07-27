import PrisonersDilemma.Bots.CupodTrollBot
import PrisonersDilemma.Bots.CupodBot
import PrisonersDilemma.Bots.DupocBot


import PrisonersDilemma.Dynamics
import PrisonersDilemma.BaseTheorems
import PrisonersDilemma.Base.Helpers
import PrisonersDilemma.Theorems.CupodTrollBot.Helpers

open PD
open PD.Bots
open PD.BaseTheorems
namespace PD.Theorems
theorem outcome_CupodTrollBot_vs_DupocBot (j k fuel : Nat)
    (hjk : (Formula.neg (.eq (DupocBot k) (CupodBot j))).size + j + 2 ≤ k) :
    outcome (fuel + 2) (CupodTrollBot j) (DupocBot k) = some (.C, .C) := by
  -- CupodTrollBot cooperates against `DupocBot` (direction A).
  have hA : play (fuel + 2) (CupodTrollBot j) (DupocBot k) = some .C :=
    CupodTrollBot_cooperates_if_opp_not_CupodBot j fuel (DupocBot k)
      (by simp [DupocBot, CupodBot])
  -- `DupocBot` cooperates with CupodTrollBot once its guard affords the floor (direction B).
  have hB : play (fuel + 2) (DupocBot k) (CupodTrollBot j) = some .C :=
    DupocBot_plays_C_against_CupodTrollBot j k fuel hjk
  exact outcome_of_plays _ _ _ _ _ hA hB

end PD.Theorems
