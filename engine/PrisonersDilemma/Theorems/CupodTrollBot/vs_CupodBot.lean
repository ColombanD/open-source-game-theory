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
-- GUARDED: the two conditions couple `k` and `fuel` (`atom_cost (fuel + 2) ≤ k` holds
-- for small fuel and fails for large), so they belong inside the statement, where both
-- are bound. Hoisting them to `∀ k fuel, …` type-checks but is FALSE, which would make
-- the theorem vacuous — the guarded template exists to prevent exactly that.
@[outcome]
theorem outcome_CupodTrollBot_vs_CupodBot :
    OutcomeSpecIf .universal 2
      (fun k fuel => (Formula.eq (CupodBot k) (CupodBot k)).size ≤ k
                     ∧ atom_cost (fuel + 2) ≤ k)
      CupodTrollBot CupodBot (some (.D, .D)) := by
  intro k fuel hside
  obtain ⟨hk, hbudget⟩ := hside
  -- Direction A: CupodTrollBot recognises CupodBot and defects.
  have hA : play (fuel + 2) (CupodTrollBot k) (CupodBot k) = some .D :=
    CupodTrollBot_defects_vs_CupodBot k fuel hk
  -- Direction B: CupodBot's own guard is satisfied (CupodTrollBot defects), so it defects too.
  have hB : play (fuel + 2) (CupodBot k) (CupodTrollBot k) = some .D :=
    CupodBot_defects_vs_CupodTrollBot k fuel hk hbudget
  exact outcome_of_plays _ _ _ _ _ hA hB

end PD.Theorems
