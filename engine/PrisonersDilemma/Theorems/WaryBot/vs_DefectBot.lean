import PrisonersDilemma.Program
import PrisonersDilemma.Dynamics
import PrisonersDilemma.Bots.LlmGenerations.WaryBot
import PrisonersDilemma.Bots.DefectBot
import PrisonersDilemma.Theorems.DefectBot.Helpers
import PrisonersDilemma.Base.Helpers
import PrisonersDilemma.Base.Asymptotics
import PrisonersDilemma.BaseTheorems
import PrisonersDilemma.Theorems.WaryBot.Helpers
import PrisonersDilemma.Outcome

open PD
open PD.BaseTheorems
open PD.Bots
namespace PD.Theorems

/-- **WaryBot vs DefectBot, the large-`k` theorem**: for every sufficiently large
    budget the refutation of DefectBot's cooperation is affordable (transcript
    `2 · log₂ k + 22` since the atom recost of 2026-09-16; it was `log₂ k + 12`) and
    WaryBot defends itself. -/
-- `k₂ ≤ k` normalizes to the template's `k₂ < k`: a sound weakening the matrix
-- never uses (it only needs SOME threshold to exist).
@[outcome]
theorem outcome_WaryBot_vs_DefectBot :
    OutcomeSpec .eventual 2
      WaryBot (fun _ => DefectBot) (some (.D, .D)) := by
  obtain ⟨K, hK⟩ := linear_log2_add_le 2 22
  refine ⟨K, fun k hk fuel => ?_⟩
  have hlog : 2 * Nat.log2 k + 22 ≤ k := by have := hK k (Nat.le_of_lt hk); omega
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

/-- A concrete defended budget: at `k = 32` the `atomNeg` transcript (DefectBot's
    D-certificate at `c_leaf + 15` — the leaf plus the positive atom's size, since the
    atom recost of 2026-09-16 — plus the negated atom's size 16) fits, and WaryBot
    defends itself. Before the recost the first defended budget was `k = 16` (cost 1 +
    guard size 15); at `k = 16` the recost transcript (30) no longer fits, and the
    bracket's upper end moved to `32` (`2 · log₂ k + 22 ≤ k` first holds at `k = 30`). -/
theorem outcome_WaryBot_vs_DefectBot_defended (fuel : Nat) :
    outcome (fuel + 2) (WaryBot 32) DefectBot = some (.D, .D) :=
  outcome_of_plays _ _ _ _ _ (WaryBot32_defects_vs_DefectBot fuel)
    (play_DefectBot (fuel + 1) _)

end PD.Theorems
