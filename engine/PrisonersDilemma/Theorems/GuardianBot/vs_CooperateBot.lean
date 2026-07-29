import PrisonersDilemma.Program
import PrisonersDilemma.Dynamics
import PrisonersDilemma.Bots.CooperateBot
import PrisonersDilemma.Bots.LlmGenerations.GuardianBot
import PrisonersDilemma.Theorems.CooperateBot.Helpers
import PrisonersDilemma.Base.Helpers
import PrisonersDilemma.BaseTheorems
import PrisonersDilemma.Theorems.GuardianBot.Helpers

open PD
open PD.BaseTheorems
open PD.Bots
namespace PD.Theorems

/-- GuardianBot vs CooperateBot: mutual cooperation at EVERY budget. The guard
    ("CooperateBot bullies the probe") is semantically false, so soundness refutes
    it outright — no Löb machinery, no floor: cooperation through norms. -/
theorem outcome_GuardianBot_vs_CooperateBot (k fuel : Nat) :
    outcome (fuel + 2) (GuardianBot k) CooperateBot = some (.C, .C) := by
  have hA : play (fuel + 2) (GuardianBot k) CooperateBot = some .C :=
    GuardianBot_cooperates_vs_CooperateBot k fuel
  have hB : play (fuel + 2) CooperateBot (GuardianBot k) = some .C :=
    play_CooperateBot (fuel + 1) _
  exact outcome_of_plays _ _ _ _ _ hA hB

end PD.Theorems
