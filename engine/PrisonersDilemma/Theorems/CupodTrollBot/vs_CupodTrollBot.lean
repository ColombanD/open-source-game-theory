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
--- CupodTrollBot ---

theorem outcome_CupodTrollBot_vs_CupodTrollBot (k fuel : Nat) :
    outcome (fuel + 3) (CupodTrollBot k) (CupodTrollBot k) = some (.C, .C) := by
  -- CupodTrollBot cooperates against itself
  have hA : play (fuel + 3) (CupodTrollBot k) (CupodTrollBot k) = some .C :=
    CupodTrollBot_cooperates_if_opp_not_CupodBot k fuel (CupodTrollBot k)
      (by simp [CupodTrollBot, CupodBot])
  simp [outcome, hA]

end PD.Theorems
