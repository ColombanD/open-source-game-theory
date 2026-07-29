import PrisonersDilemma.Program
import PrisonersDilemma.Dynamics
import PrisonersDilemma.Bots.LlmGenerations.WaryBot
import PrisonersDilemma.Bots.EBot
import PrisonersDilemma.Base.Helpers
import PrisonersDilemma.BaseTheorems
import PrisonersDilemma.Theorems.WaryBot.Helpers

open PD
open PD.BaseTheorems
open PD.Bots
namespace PD.Theorems

/-- WaryBot 2 vs EBot: the honest `(C, D)` — EBot's DefectBot probe catches
    the floor-trust and defects immediately. -/
theorem outcome_WaryBot_vs_EBot (fuel : Nat) :
    outcome (fuel + 4) (WaryBot 2) EBot = some (.C, .D) := by
  have hA : play (fuel + 4) (WaryBot 2) EBot = some .C := by
    simpa [Nat.add_assoc] using
      WaryBot_cooperates_floor 2 (fuel + 2) EBot (by decide)
  exact outcome_of_plays _ _ _ _ _ hA (EBot_plays_D_against_WaryBot2 fuel)
end PD.Theorems
