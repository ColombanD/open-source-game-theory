import PrisonersDilemma.Bots.CupodTrollBot
import PrisonersDilemma.Bots.CupodBot


import PrisonersDilemma.Dynamics
import PrisonersDilemma.BaseTheorems
import PrisonersDilemma.Base.Helpers
import PrisonersDilemma.Theorems.CupodTrollBot.Helpers
import PrisonersDilemma.Outcome

open PD
open PD.Bots
open PD.BaseTheorems
namespace PD.Theorems
--- CupodTrollBot ---

@[outcome]
theorem outcome_CupodTrollBot_vs_CupodTrollBot :
    OutcomeSpec .universal 3
      CupodTrollBot CupodTrollBot (some (.C, .C)) := by
  intro k fuel
  -- CupodTrollBot cooperates against itself
  have hA : play (fuel + 3) (CupodTrollBot k) (CupodTrollBot k) = some .C :=
    CupodTrollBot_cooperates_if_opp_not_CupodBot k fuel (CupodTrollBot k)
      (by simp [CupodTrollBot, CupodBot])
  simp [outcome, hA]

end PD.Theorems
