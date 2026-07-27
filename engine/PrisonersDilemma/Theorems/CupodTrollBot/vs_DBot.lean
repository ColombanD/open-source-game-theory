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
theorem outcome_CupodTrollBot_vs_DBot (k fuel : Nat) :
    outcome (fuel + 4) (CupodTrollBot k) DBot = some (.C, .D) := by
  -- CupodTrollBot cooperates against `DBot` (direction A).
  have hA : play (fuel + 4) (CupodTrollBot k) DBot = some .C :=
    CupodTrollBot_cooperates_if_opp_not_CupodBot k (fuel + 2) DBot
      (by simp [DBot, CupodBot])
  -- `DBot` defects against CupodTrollBot (direction B).
  have hB : play (fuel + 4) DBot (CupodTrollBot k) = some .D :=
    DBot_plays_D_against_CupodTrollBot k fuel
  exact outcome_of_plays _ _ _ _ _ hA hB

end PD.Theorems
