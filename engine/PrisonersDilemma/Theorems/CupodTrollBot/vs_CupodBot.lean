import PrisonersDilemma.Bots.CupodTrollBot
import PrisonersDilemma.Bots.CupodBot


import PrisonersDilemma.Dynamics
import PrisonersDilemma.BaseTheorems
import PrisonersDilemma.Base.Helpers
import PrisonersDilemma.Theorems.CupodTrollBot.Helpers

open PD
open PD.Bots
open PD.BaseTheorems
namespace PD.Theorems
theorem outcome_CupodTrollBot_vs_CupodBot (k fuel : Nat)
    (hk : (Formula.eq (CupodBot k) (CupodBot k)).size ≤ k)
    (hbudget : atom_cost (fuel + 2) ≤ k) :
    outcome (fuel + 2) (CupodTrollBot k) (CupodBot k) = some (.D, .D) := by
  -- Direction A: CupodTrollBot recognises CupodBot and defects.
  have hA : play (fuel + 2) (CupodTrollBot k) (CupodBot k) = some .D :=
    CupodTrollBot_defects_vs_CupodBot k fuel hk
  -- Direction B: CupodBot's own guard is satisfied (CupodTrollBot defects), so it defects too.
  have hB : play (fuel + 2) (CupodBot k) (CupodTrollBot k) = some .D :=
    CupodBot_defects_vs_CupodTrollBot k fuel hk hbudget
  exact outcome_of_plays _ _ _ _ _ hA hB

end PD.Theorems
