import PrisonersDilemma.Program
import PrisonersDilemma.Dynamics
import PrisonersDilemma.Bots.DefectBot
import PrisonersDilemma.Bots.LlmGenerations.GuardianBot
import PrisonersDilemma.Theorems.DefectBot.Helpers
import PrisonersDilemma.Base.Helpers
import PrisonersDilemma.BaseTheorems
import PrisonersDilemma.Theorems.GuardianBot.Helpers
import PrisonersDilemma.Outcome

open PD
open PD.BaseTheorems
open PD.Bots
namespace PD.Theorems

/-- GuardianBot vs DefectBot: the norm enforcer punishes the provable bully.
    DefectBot's defection against the CooperateBot probe is a bare `.const`
    certificate, so the guard fires at every budget `k ≥ 5` (the leaf plus the atom's
    size, since the atom recost of 2026-09-16; it was `k ≥ 1`) — a budget FLOOR, hence
    `.eventual` (threshold 4), not a stagger. (Until 2026-08-26 this was stated as
    `∀ k, … (GuardianBot (k + 1))`, which the linter read as a staggered budget.) -/
@[outcome]
theorem outcome_GuardianBot_vs_DefectBot :
    OutcomeSpec .eventual 2 GuardianBot (fun _ => DefectBot) (some (.D, .D)) := by
  refine ⟨4, fun k hk fuel => ?_⟩
  obtain ⟨k', rfl⟩ : ∃ k', k = k' + 5 := ⟨k - 5, by omega⟩
  have hA : play (fuel + 2) (GuardianBot (k' + 5)) DefectBot = some .D :=
    GuardianBot_defects_vs_DefectBot k' fuel
  have hB : play (fuel + 2) DefectBot (GuardianBot (k' + 5)) = some .D :=
    play_DefectBot (fuel + 1) _
  exact outcome_of_plays _ _ _ _ _ hA hB

end PD.Theorems
