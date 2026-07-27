import PrisonersDilemma.Bots.CupodTrollBot
import PrisonersDilemma.Bots.CupodBot
import PrisonersDilemma.Bots.EBot


import PrisonersDilemma.Dynamics
import PrisonersDilemma.BaseTheorems
import PrisonersDilemma.Base.Helpers
import PrisonersDilemma.Theorems.CupodTrollBot.Helpers

open PD
open PD.Bots
open PD.BaseTheorems
namespace PD.Theorems
theorem outcome_CupodTrollBot_vs_EBot (k fuel : Nat) :
    outcome (fuel + 4) (CupodTrollBot k) EBot = some (.C, .D) := by
  -- CupodTrollBot cooperates against `EBot` (direction A).
  have hA : play (fuel + 4) (CupodTrollBot k) EBot = some .C :=
    CupodTrollBot_cooperates_if_opp_not_CupodBot k (fuel + 2) EBot
      (by simp [EBot, CupodBot])
  -- `EBot` defects against CupodTrollBot (direction B).
  have hB : play (fuel + 4) EBot (CupodTrollBot k) = some .D :=
    EBot_plays_D_against_CupodTrollBot k fuel
  exact outcome_of_plays _ _ _ _ _ hA hB

end PD.Theorems
