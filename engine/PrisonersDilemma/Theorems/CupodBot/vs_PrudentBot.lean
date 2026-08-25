import PrisonersDilemma.Theorems.PrudentBot.vs_CupodBot

open PD
open PD.BaseTheorems
open PD.Bots
namespace PD.Theorems

/-- **CupodBot vs PrudentBot = (C, D)** at every same budget — the transpose of
    `outcome_PrudentBot_vs_CupodBot` (`Theorems/PrudentBot/vs_CupodBot.lean`). -/
theorem outcome_CupodBot_vs_PrudentBot (k fuel : Nat) :
    outcome (fuel + 2) (CupodBot k) (PrudentBot k) = some (.C, .D) :=
  outcome_of_plays _ _ _ _ _ (CupodBot_plays_C_against_PrudentBot k fuel)
    (PrudentBot_plays_D_against_CupodBot k fuel)

end PD.Theorems
