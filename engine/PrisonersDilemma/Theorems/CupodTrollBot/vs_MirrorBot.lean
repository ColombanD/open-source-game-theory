import PrisonersDilemma.Bots.CupodTrollBot
import PrisonersDilemma.Bots.CupodBot
import PrisonersDilemma.Bots.MirrorBot


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
theorem outcome_CupodTrollBot_vs_MirrorBot :
    OutcomeSpec .universal 3
      CupodTrollBot (fun _ => MirrorBot) (some (.C, .C)) := by
  intro k fuel
  -- CupodTrollBot cooperates against `MirrorBot` (direction A).
  have hA : play (fuel + 3) (CupodTrollBot k) MirrorBot = some .C :=
    CupodTrollBot_cooperates_if_opp_not_CupodBot k (fuel + 1) MirrorBot
      (by simp [MirrorBot, CupodBot])
  -- `MirrorBot` mirrors CupodTrollBot's cooperation (direction B).
  have hB : play (fuel + 3) MirrorBot (CupodTrollBot k) = some .C :=
    MirrorBot_plays_C_against_CupodTrollBot k fuel
  exact outcome_of_plays _ _ _ _ _ hA hB

end PD.Theorems
