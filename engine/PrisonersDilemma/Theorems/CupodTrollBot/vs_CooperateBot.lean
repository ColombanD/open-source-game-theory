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
--- CooperateBot ---

theorem outcome_CupodTrollBot_vs_CooperateBot (k fuel : Nat) :
    outcome (fuel + 2) (CupodTrollBot k) CooperateBot = some (.C, .C) := by
  -- CupodTrollBot cooperates against `CooperateBot` (direction A).
  have hA : play (fuel + 2) (CupodTrollBot k) CooperateBot = some .C :=
    CupodTrollBot_cooperates_if_opp_not_CupodBot k fuel (CooperateBot)
      (by simp [CooperateBot, CupodBot])
  -- `CooperateBot` cooperates against CupodTrollBot (direction B).
  have hB : play (fuel + 2) CooperateBot (CupodTrollBot k) = some .C := rfl
  exact outcome_of_plays _ _ _ _ _ hA hB

end PD.Theorems
