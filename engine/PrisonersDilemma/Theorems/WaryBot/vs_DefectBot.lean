import PrisonersDilemma.Program
import PrisonersDilemma.Dynamics
import PrisonersDilemma.Bots.LlmGenerations.WaryBot
import PrisonersDilemma.Bots.DefectBot
import PrisonersDilemma.Theorems.DefectBot.Helpers
import PrisonersDilemma.Base.Helpers
import PrisonersDilemma.Base.Asymptotics
import PrisonersDilemma.BaseTheorems
import PrisonersDilemma.Theorems.WaryBot.Helpers

open PD
open PD.BaseTheorems
open PD.Bots
namespace PD.Theorems

/-- **WaryBot vs DefectBot, the large-`k` theorem**: for every sufficiently large
    budget the refutation of DefectBot's cooperation is affordable (transcript
    `log₂ k + 12`) and WaryBot defends itself. -/
theorem outcome_WaryBot_vs_DefectBot (fuel : Nat) :
    ∃ k₂, ∀ k, k₂ ≤ k →
      outcome (fuel + 2) (WaryBot k) DefectBot = some (.D, .D) := by
  obtain ⟨K, hK⟩ := linear_log2_add_le 1 12
  refine ⟨K, fun k hk => ?_⟩
  have hlog : Nat.log2 k + 12 ≤ k := by have := hK k hk; omega
  exact outcome_of_plays _ _ _ _ _
    (WaryBot_defects_vs_DefectBot_large k fuel hlog)
    (play_DefectBot (fuel + 1) _)

/-- **The floor side of the phase transition**: at `k = 2` WaryBot cannot afford
    the refutation (guard size 12 > 2), trusts, and is EXPLOITED. Together with
    the large-`k` theorem above this brackets the machine-checked budget
    threshold. -/
theorem outcome_WaryBot_vs_DefectBot_floor (fuel : Nat) :
    outcome (fuel + 2) (WaryBot 2) DefectBot = some (.C, .D) :=
  outcome_of_plays _ _ _ _ _ (WaryBot_cooperates_floor 2 fuel _ (by decide))
    (play_DefectBot (fuel + 1) _)

/-- The concrete first defended budget: `k = 16` is exactly where the `atomNeg`
    transcript (cost 1 + guard size 15) fits. -/
theorem outcome_WaryBot_vs_DefectBot_defended (fuel : Nat) :
    outcome (fuel + 2) (WaryBot 16) DefectBot = some (.D, .D) :=
  outcome_of_plays _ _ _ _ _ (WaryBot16_defects_vs_DefectBot fuel)
    (play_DefectBot (fuel + 1) _)

end PD.Theorems
