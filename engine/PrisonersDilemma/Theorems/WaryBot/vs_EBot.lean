import PrisonersDilemma.Program
import PrisonersDilemma.Dynamics
import PrisonersDilemma.Bots.LlmGenerations.WaryBot
import PrisonersDilemma.Bots.EBot
import PrisonersDilemma.Base.Helpers
import PrisonersDilemma.Base.Asymptotics
import PrisonersDilemma.BaseTheorems
import PrisonersDilemma.Theorems.WaryBot.Helpers

open PD
open PD.BaseTheorems
open PD.Bots
namespace PD.Theorems

/-- **WaryBot vs EBot, the large-`k` theorem — the outcome FLIPS with the
    budget**: a defended WaryBot fails EBot's exploit test (first probe) and
    passes its niceness test (second probe), so EBot cooperates, irrefutably.
    This settles structurally the cell the deterministic pre-pass could only
    certify at `k = 32`. Compare `_floor`. -/
theorem outcome_WaryBot_vs_EBot (fuel : Nat) :
    ∃ k₂, ∀ k, k₂ ≤ k →
      outcome (fuel + 5) (WaryBot k) EBot = some (.C, .C) := by
  obtain ⟨K, hK⟩ := linear_log2_add_le 1 14
  refine ⟨K, fun k hk => ?_⟩
  have hlog : Nat.log2 k + 14 ≤ k := by have := hK k hk; omega
  have hA : play (fuel + 5) (WaryBot k) EBot = some .C := by
    simpa [Nat.add_assoc] using WaryBot_cooperates_vs_EBot_large k (fuel + 3) hlog
  exact outcome_of_plays _ _ _ _ _ hA (EBot_plays_C_against_WaryBot_large k fuel hlog)

/-- **The floor side, the whole regime**: at every budget below the guard sizes
    EBot's DefectBot probe catches the floor-trust and defects immediately. -/
theorem outcome_WaryBot_vs_EBot_floor (k fuel : Nat)
    (hszDB : k < (Formula.neg (.plays (.bot DefectBot) (WaryBot k) .C)).size)
    (hszE : k < (Formula.neg (.plays EBot (WaryBot k) .C)).size) :
    outcome (fuel + 4) (WaryBot k) EBot = some (.C, .D) := by
  have hA : play (fuel + 4) (WaryBot k) EBot = some .C := by
    simpa [Nat.add_assoc] using
      WaryBot_cooperates_floor k (fuel + 2) EBot hszE
  exact outcome_of_plays _ _ _ _ _ hA
    (EBot_plays_D_against_WaryBot_floor k fuel hszDB)

/-- The concrete `k = 2` instance. -/
theorem outcome_WaryBot_vs_EBot_floor2 (fuel : Nat) :
    outcome (fuel + 4) (WaryBot 2) EBot = some (.C, .D) :=
  outcome_WaryBot_vs_EBot_floor 2 fuel (by decide) (by decide)

end PD.Theorems
