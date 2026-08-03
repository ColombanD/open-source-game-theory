import PrisonersDilemma.Program
import PrisonersDilemma.Dynamics
import PrisonersDilemma.Bots.LlmGenerations.WaryBot
import PrisonersDilemma.Bots.LlmGenerations.GuardianBot
import PrisonersDilemma.Bots.CooperateBot
import PrisonersDilemma.Base.Helpers
import PrisonersDilemma.BaseTheorems
import PrisonersDilemma.Theorems.WaryBot.Helpers

open PD
open PD.BaseTheorems
open PD.Bots
namespace PD.Theorems

/-- GuardianBot's guard against WaryBot ("WaryBot bullies CooperateBot") is
    semantically false: WaryBot cooperates with the probe. -/
theorem wg_guardian_guard_false (k : Nat) :
    proofSearch k (.plays (WaryBot k) (.bot CooperateBot) .D) = false := by
  cases hps : proofSearch k (.plays (WaryBot k) (.bot CooperateBot) .D) with
  | true =>
      exfalso
      obtain ⟨n, hn⟩ := proofSearch_sound _ _ hps
      have hC : play (n + 2) (WaryBot k) (.bot CooperateBot) = some .C :=
        WaryBot_cooperates_vs_botCooperateBot k n
      have hD : play (n + 2) (WaryBot k) (.bot CooperateBot) = some .D :=
        eval_mono_le hn (n + 2) (by omega)
      rw [hC] at hD; simp at hD
  | false => rfl

/-- GuardianBot cooperates with WaryBot (guard refuted). -/
theorem wg_GuardianBot_cooperates_vs_WaryBot (k fuel : Nat) :
    play (fuel + 2) (GuardianBot k) (WaryBot k) = some .C := by
  have hg := wg_guardian_guard_false k
  show eval (fuel + 2) (GuardianBot k) (WaryBot k) (GuardianBot k) = some .C
  unfold GuardianBot
  simp [eval, Prog.subst, Formula.subst, hg]

/-- WaryBot's guard against GuardianBot ("GuardianBot does NOT cooperate with
    WaryBot") is semantically false: GuardianBot cooperates. -/
theorem wg_wary_guard_false (k : Nat) :
    proofSearch k (.neg (.plays (GuardianBot k) (WaryBot k) .C)) = false := by
  cases hps : proofSearch k (.neg (.plays (GuardianBot k) (WaryBot k) .C)) with
  | true =>
      have hI : (Formula.plays (GuardianBot k) (WaryBot k) .C).interp := by
        unfold Formula.interp
        exact ⟨2, wg_GuardianBot_cooperates_vs_WaryBot k 0⟩
      exact absurd hI (proofSearch_sound _ _ hps)
  | false => rfl

/-- WaryBot cooperates with GuardianBot (cannot refute its cooperation). -/
theorem wg_WaryBot_cooperates_vs_GuardianBot (k fuel : Nat) :
    play (fuel + 2) (WaryBot k) (GuardianBot k) = some .C := by
  have hg := wg_wary_guard_false k
  show eval (fuel + 2) (WaryBot k) (GuardianBot k) (WaryBot k) = some .C
  unfold WaryBot at hg ⊢
  simp [eval, Prog.subst, Formula.subst, hg]

theorem llm_outcome_WaryBot_vs_GuardianBot :
    ∃ k₂, ∀ k, k₂ < k →
      ∃ fuel, outcome fuel (WaryBot k) (GuardianBot k) = some (.C, .C) := by
  refine ⟨0, fun k _ => ⟨2, ?_⟩⟩
  have hA : play 2 (WaryBot k) (GuardianBot k) = some .C :=
    wg_WaryBot_cooperates_vs_GuardianBot k 0
  have hB : play 2 (GuardianBot k) (WaryBot k) = some .C :=
    wg_GuardianBot_cooperates_vs_WaryBot k 0
  exact outcome_of_plays _ _ _ _ _ hA hB

end PD.Theorems

