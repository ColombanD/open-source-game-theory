import PrisonersDilemma.Bots.CupodTrollBot
import PrisonersDilemma.Bots.CupodBot
import PrisonersDilemma.Bots.DupocBot


import PrisonersDilemma.Dynamics
import PrisonersDilemma.BaseTheorems
import PrisonersDilemma.Base.Helpers
import PrisonersDilemma.Theorems.CupodTrollBot.Helpers
import PrisonersDilemma.Outcome

open PD
open PD.Bots
open PD.BaseTheorems
namespace PD.Theorems
-- `j` is CupodTrollBot's own budget and stays a free binder; `k` is the migrated one.
-- The size condition couples them, so it rides in the guarded template's `side`.
-- (An earlier pass excluded this cell as a "two independent budgets" template limit —
-- that was wrong: only ONE of the two needs to be the template's budget.)
@[outcome]
theorem outcome_CupodTrollBot_vs_DupocBot (j : Nat) :
    OutcomeSpecIf .universal 2
      (fun k _ => (Formula.neg (.eq (DupocBot k) (CupodBot j))).size + j + 2 ≤ k)
      (fun _ => CupodTrollBot j) DupocBot (some (.C, .C)) := by
  intro k fuel hjk
  -- CupodTrollBot cooperates against `DupocBot` (direction A).
  have hA : play (fuel + 2) (CupodTrollBot j) (DupocBot k) = some .C :=
    CupodTrollBot_cooperates_if_opp_not_CupodBot j fuel (DupocBot k)
      (by simp [DupocBot, CupodBot])
  -- `DupocBot` cooperates with CupodTrollBot once its guard affords the floor (direction B).
  have hB : play (fuel + 2) (DupocBot k) (CupodTrollBot j) = some .C :=
    DupocBot_plays_C_against_CupodTrollBot j k fuel hjk
  exact outcome_of_plays _ _ _ _ _ hA hB

end PD.Theorems
