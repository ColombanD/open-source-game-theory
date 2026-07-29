import PrisonersDilemma.Program
import PrisonersDilemma.Dynamics
import PrisonersDilemma.Bots.LlmGenerations.WaryBot
import PrisonersDilemma.Bots.DBot
import PrisonersDilemma.Base.Helpers
import PrisonersDilemma.Base.Asymptotics
import PrisonersDilemma.BaseTheorems
import PrisonersDilemma.Theorems.WaryBot.Helpers

open PD
open PD.BaseTheorems
open PD.Bots
namespace PD.Theorems

/-- **WaryBot vs DBot, the large-`k` theorem — the outcome FLIPS with the
    budget**: once WaryBot can afford to defend against the DefectBot probe
    (transcript `log₂ k + 14`), DBot sees no sucker and cooperates, and DBot's
    cooperation is in turn irrefutable — mutual cooperation. Compare `_floor`. -/
theorem outcome_WaryBot_vs_DBot (fuel : Nat) :
    ∃ k₂, ∀ k, k₂ ≤ k →
      outcome (fuel + 4) (WaryBot k) DBot = some (.C, .C) := by
  obtain ⟨K, hK⟩ := linear_log2_add_le 1 14
  refine ⟨K, fun k hk => ?_⟩
  have hlog : Nat.log2 k + 14 ≤ k := by have := hK k hk; omega
  have hA : play (fuel + 4) (WaryBot k) DBot = some .C := by
    simpa [Nat.add_assoc] using WaryBot_cooperates_vs_DBot_large k (fuel + 2) hlog
  exact outcome_of_plays _ _ _ _ _ hA (DBot_plays_C_against_WaryBot_large k fuel hlog)

/-- **The floor side, the whole regime**: at every budget below the guard sizes
    DBot's probe catches WaryBot cooperating with DefectBot and exploits it. -/
theorem outcome_WaryBot_vs_DBot_floor (k fuel : Nat)
    (hszDB : k < (Formula.neg (.plays (.bot DefectBot) (WaryBot k) .C)).size)
    (hszD : k < (Formula.neg (.plays DBot (WaryBot k) .C)).size) :
    outcome (fuel + 4) (WaryBot k) DBot = some (.C, .D) := by
  have hA : play (fuel + 4) (WaryBot k) DBot = some .C := by
    simpa [Nat.add_assoc] using
      WaryBot_cooperates_floor k (fuel + 2) DBot hszD
  exact outcome_of_plays _ _ _ _ _ hA
    (DBot_plays_D_against_WaryBot_floor k fuel hszDB)

/-- The concrete `k = 2` instance. -/
theorem outcome_WaryBot_vs_DBot_floor2 (fuel : Nat) :
    outcome (fuel + 4) (WaryBot 2) DBot = some (.C, .D) :=
  outcome_WaryBot_vs_DBot_floor 2 fuel (by decide) (by decide)

end PD.Theorems
