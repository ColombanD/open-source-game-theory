import PrisonersDilemma.Theorems.PrudentBot.vs_CupodBot
import PrisonersDilemma.Outcome

open PD
open PD.BaseTheorems
open PD.Bots
namespace PD.Theorems

/-- **CupodBot vs PrudentBot = (C, D)** at every same budget — the transpose of
    `outcome_PrudentBot_vs_CupodBot` (`Theorems/PrudentBot/vs_CupodBot.lean`). -/
@[outcome]
theorem outcome_CupodBot_vs_PrudentBot :
    OutcomeSpec .universal 2
      CupodBot PrudentBot (some (.C, .D)) :=
  fun k fuel =>
  outcome_of_plays _ _ _ _ _ (CupodBot_plays_C_against_PrudentBot k fuel)
    (PrudentBot_plays_D_against_CupodBot k fuel)

end PD.Theorems
