import PrisonersDilemma.Bots.CupodTrollBot
import PrisonersDilemma.Bots.CupodBot
import PrisonersDilemma.Bots.EBot


import PrisonersDilemma.Dynamics
import PrisonersDilemma.BaseTheorems
import PrisonersDilemma.Base.Helpers
import PrisonersDilemma.Theorems.CupodTrollBot.Helpers
import PrisonersDilemma.Outcome

open PD
open PD.Bots
open PD.BaseTheorems
namespace PD.Theorems
@[outcome]
theorem outcome_CupodTrollBot_vs_EBot :
    OutcomeSpec .universal 4
      CupodTrollBot (fun _ => EBot) (some (.C, .D)) := by
  intro k fuel
  -- CupodTrollBot cooperates against `EBot` (direction A).
  have hA : play (fuel + 4) (CupodTrollBot k) EBot = some .C :=
    CupodTrollBot_cooperates_if_opp_not_CupodBot k (fuel + 2) EBot
      (by simp [EBot, CupodBot])
  -- `EBot` defects against CupodTrollBot (direction B).
  have hB : play (fuel + 4) EBot (CupodTrollBot k) = some .D :=
    EBot_plays_D_against_CupodTrollBot k fuel
  exact outcome_of_plays _ _ _ _ _ hA hB

end PD.Theorems
