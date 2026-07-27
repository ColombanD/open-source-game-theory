import PrisonersDilemma.Bots.CupodTrollBot
import PrisonersDilemma.Bots.CupodBot
import PrisonersDilemma.Bots.MirrorBot


import PrisonersDilemma.Dynamics
import PrisonersDilemma.BaseTheorems
import PrisonersDilemma.Base.Helpers
import PrisonersDilemma.Theorems.CupodTrollBot.Helpers

open PD
open PD.Bots
open PD.BaseTheorems
namespace PD.Theorems
theorem outcome_CupodTrollBot_vs_MirrorBot (k fuel : Nat) :
    outcome (fuel + 3) (CupodTrollBot k) MirrorBot = some (.C, .C) := by
  -- CupodTrollBot cooperates against `MirrorBot` (direction A).
  have hA : play (fuel + 3) (CupodTrollBot k) MirrorBot = some .C :=
    CupodTrollBot_cooperates_if_opp_not_CupodBot k (fuel + 1) MirrorBot
      (by simp [MirrorBot, CupodBot])
  -- `MirrorBot` mirrors CupodTrollBot's cooperation (direction B).
  have hB : play (fuel + 3) MirrorBot (CupodTrollBot k) = some .C :=
    MirrorBot_plays_C_against_CupodTrollBot k fuel
  exact outcome_of_plays _ _ _ _ _ hA hB

end PD.Theorems
