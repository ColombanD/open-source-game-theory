import PrisonersDilemma.Bots.CupodTrollBot
import PrisonersDilemma.Bots.CooperateBot
import PrisonersDilemma.Bots.DefectBot
import PrisonersDilemma.Bots.CupodBot
import PrisonersDilemma.Bots.DupocBot
import PrisonersDilemma.Bots.DBot
import PrisonersDilemma.Bots.EBot
import PrisonersDilemma.Bots.MirrorBot
import PrisonersDilemma.Bots.OBot
import PrisonersDilemma.Bots.TitForTatBot


import PrisonersDilemma.Dynamics
import PrisonersDilemma.BaseTheorems
import PrisonersDilemma.Base.Helpers
import PrisonersDilemma.Theorems.CupodTrollBot.Helpers

open PD
open PD.Bots
open PD.BaseTheorems
namespace PD.Theorems
theorem outcome_CupodTrollBot_vs_OBot (k fuel : Nat) :
    outcome (fuel + 5) (CupodTrollBot k) OBot = some (.C, .C) := by
  -- CupodTrollBot cooperates against `OBot` (direction A).
  have hA : play (fuel + 5) (CupodTrollBot k) OBot = some .C :=
    CupodTrollBot_cooperates_if_opp_not_CupodBot k (fuel + 3) OBot
      (by simp [OBot, CupodBot])
  -- `OBot` cooperates with CupodTrollBot (direction B).
  have hB : play (fuel + 5) OBot (CupodTrollBot k) = some .C :=
    OBot_plays_C_against_CupodTrollBot k fuel
  exact outcome_of_plays _ _ _ _ _ hA hB

end PD.Theorems
