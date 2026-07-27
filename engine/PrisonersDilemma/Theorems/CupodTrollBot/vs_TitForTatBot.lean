import PrisonersDilemma.Bots.CupodTrollBot
import PrisonersDilemma.Bots.CupodBot
import PrisonersDilemma.Bots.TitForTatBot


import PrisonersDilemma.Dynamics
import PrisonersDilemma.BaseTheorems
import PrisonersDilemma.Base.Helpers
import PrisonersDilemma.Theorems.CupodTrollBot.Helpers

open PD
open PD.Bots
open PD.BaseTheorems
namespace PD.Theorems
theorem outcome_CupodTrollBot_vs_TitForTatBot (k fuel : Nat) :
    outcome (fuel + 4) (CupodTrollBot k) TitForTatBot = some (.C, .C) := by
  -- CupodTrollBot cooperates against `TitForTatBot` (direction A).
  have hA : play (fuel + 4) (CupodTrollBot k) TitForTatBot = some .C :=
    CupodTrollBot_cooperates_if_opp_not_CupodBot k (fuel + 2) (TitForTatBot)
      (by simp [TitForTatBot, CupodBot])
  -- `TitForTatBot` cooperates against CupodTrollBot (direction B).
  have hB : play (fuel + 4) TitForTatBot (CupodTrollBot k) = some .C :=
    TitForTatBot_plays_C_against_CupodTrollBot k fuel
  exact outcome_of_plays _ _ _ _ _ hA hB

end PD.Theorems
