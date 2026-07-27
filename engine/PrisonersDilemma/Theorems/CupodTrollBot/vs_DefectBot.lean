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
--- DefectBot ---

theorem outcome_CupodTrollBot_vs_DefectBot (k fuel : Nat) :
    outcome (fuel + 2) (CupodTrollBot k) DefectBot = some (.C, .D) := by
  -- CupodTrollBot cooperates against `DefectBot` (direction A).
  have hA : play (fuel + 2) (CupodTrollBot k) DefectBot = some .C :=
    CupodTrollBot_cooperates_if_opp_not_CupodBot k fuel (DefectBot)
      (by simp [DefectBot, CupodBot])
  -- `DefectBot` defects against CupodTrollBot (direction B).
  have hB : play (fuel + 2) DefectBot (CupodTrollBot k) = some .D := rfl
  exact outcome_of_plays _ _ _ _ _ hA hB

end PD.Theorems
