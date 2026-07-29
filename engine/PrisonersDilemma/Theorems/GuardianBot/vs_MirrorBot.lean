import PrisonersDilemma.Program
import PrisonersDilemma.Dynamics
import PrisonersDilemma.Bots.MirrorBot
import PrisonersDilemma.Bots.LlmGenerations.GuardianBot
import PrisonersDilemma.Base.Helpers
import PrisonersDilemma.BaseTheorems
import PrisonersDilemma.Theorems.GuardianBot.Helpers

open PD
open PD.BaseTheorems
open PD.Bots
namespace PD.Theorems

/-- GuardianBot vs MirrorBot: mutual cooperation at EVERY budget, with NO Löbian
    fixpoint between the players — the guard is about the frozen third-party probe,
    which MirrorBot provably-never bullies (soundness refutation), and MirrorBot's
    simulation reaches GuardianBot's trusting else-branch. Cooperation through
    norms rather than mutual proof of cooperation. -/
theorem outcome_GuardianBot_vs_MirrorBot (k fuel : Nat) :
    outcome (fuel + 3) (GuardianBot k) MirrorBot = some (.C, .C) := by
  have hA : play (fuel + 3) (GuardianBot k) MirrorBot = some .C := by
    simpa [Nat.add_assoc] using GuardianBot_cooperates_vs_MirrorBot k (fuel + 1)
  have hB : play (fuel + 3) MirrorBot (GuardianBot k) = some .C :=
    MirrorBot_plays_C_against_GuardianBot k fuel
  exact outcome_of_plays _ _ _ _ _ hA hB

end PD.Theorems
