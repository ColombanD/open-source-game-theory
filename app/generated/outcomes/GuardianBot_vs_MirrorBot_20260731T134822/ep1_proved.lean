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

theorem llm_outcome_GuardianBot_vs_MirrorBot :
    ∃ k₂, ∀ k, k₂ < k →
      ∃ fuel, outcome fuel (GuardianBot k) MirrorBot = some (.C, .C) := by
  refine ⟨0, fun k _ => ⟨3, ?_⟩⟩
  have hA : play 3 (GuardianBot k) MirrorBot = some .C := by
    simpa using GuardianBot_cooperates_vs_MirrorBot k 1
  have hB : play 3 MirrorBot (GuardianBot k) = some .C := by
    simpa using MirrorBot_plays_C_against_GuardianBot k 0
  exact outcome_of_plays _ _ _ _ _ hA hB

end PD.Theorems

