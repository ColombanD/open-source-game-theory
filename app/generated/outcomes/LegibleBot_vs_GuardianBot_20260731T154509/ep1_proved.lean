import PrisonersDilemma.Program
import PrisonersDilemma.Dynamics
import PrisonersDilemma.Bots.LlmGenerations.LegibleBot
import PrisonersDilemma.Bots.LlmGenerations.GuardianBot
import PrisonersDilemma.Bots.CooperateBot
import PrisonersDilemma.Base.Helpers
import PrisonersDilemma.BaseTheorems
import PrisonersDilemma.Theorems.LegibleBot.Helpers
import PrisonersDilemma.Theorems.GuardianBot.Helpers

open PD
open PD.BaseTheorems
open PD.Bots
namespace PD.Theorems

/-- LegibleBot cooperates with `.bot CooperateBot` at large `k`. -/
theorem lg_legible_C_vs_botCB :
    ∃ k₂, ∀ k, k > k₂ →
      ∃ n, play n (LegibleBot (2*k+64) k) (.bot CooperateBot) = some .C := by
  apply LegibleBot_cooperates_large (fun _ => .bot CooperateBot) 100
  intro k
  simp only [CooperateBot, Prog.size]
  omega

/-- GuardianBot's guard against LegibleBot is refuted: LegibleBot doesn't bully the probe. -/
theorem lg_guardian_guard_false :
    ∃ k₂, ∀ k, k > k₂ →
      proofSearch k (.plays (LegibleBot (2*k+64) k) (.bot CooperateBot) .D) = false := by
  obtain ⟨k₂, h⟩ := lg_legible_C_vs_botCB
  refine ⟨k₂, fun k hk => ?_⟩
  cases hps : proofSearch k (.plays (LegibleBot (2*k+64) k) (.bot CooperateBot) .D) with
  | false => rfl
  | true =>
      exfalso
      obtain ⟨n, hn⟩ := proofSearch_sound _ _ hps
      obtain ⟨m, hm⟩ := h k hk
      have hC : play (max n m) (LegibleBot (2*k+64) k) (.bot CooperateBot) = some .C :=
        eval_mono_le hm (max n m) (Nat.le_max_right _ _)
      have hD : play (max n m) (LegibleBot (2*k+64) k) (.bot CooperateBot) = some .D :=
        eval_mono_le hn (max n m) (Nat.le_max_left _ _)
      rw [hC] at hD; simp at hD

/-- With the guard refuted, GuardianBot trusts LegibleBot (else-branch C). -/
theorem lg_guardian_C_vs_legible (k fuel : Nat)
    (hg : proofSearch k (.plays (LegibleBot (2*k+64) k) (.bot CooperateBot) .D) = false) :
    play (fuel + 2) (GuardianBot k) (LegibleBot (2*k+64) k) = some .C := by
  show eval (fuel + 2) (GuardianBot k) (LegibleBot (2*k+64) k) (GuardianBot k) = some .C
  unfold GuardianBot
  simp [eval, Prog.subst, Formula.subst, hg]

/-- LegibleBot cooperates with GuardianBot at large `k` (opponent-generic Löb). -/
theorem lg_legible_C_vs_guardian :
    ∃ k₂, ∀ k, k > k₂ →
      ∃ n, play n (LegibleBot (2*k+64) k) (GuardianBot k) = some .C := by
  apply LegibleBot_cooperates_large (fun k => GuardianBot k) 100
  intro k
  simp only [GuardianBot, CooperateBot, Prog.size, Formula.size, numCost]
  omega

/-- **LegibleBot (staggered) vs GuardianBot → (C, C)** for all sufficiently large `k`:
    LegibleBot's cooperation becomes legible (bounded Löb through two boxes) so it
    trusts GuardianBot; and GuardianBot, unable to prove that LegibleBot bullies
    CooperateBot (it doesn't — it cooperates with everyone), trusts back. -/
theorem llm_outcome_LegibleBot_vs_GuardianBot :
    ∃ k₂, ∀ k, k₂ < k →
      ∃ fuel, outcome fuel (LegibleBot (2*k+64) k) (GuardianBot k) = some (.C, .C) := by
  obtain ⟨k₁, hguard⟩ := lg_guardian_guard_false
  obtain ⟨k₂, hleg⟩ := lg_legible_C_vs_guardian
  refine ⟨max k₁ k₂, fun k hk => ?_⟩
  have hk1 : k > k₁ := lt_of_le_of_lt (Nat.le_max_left _ _) hk
  have hk2 : k > k₂ := lt_of_le_of_lt (Nat.le_max_right _ _) hk
  obtain ⟨n, hn⟩ := hleg k hk2
  have hgf := hguard k hk1
  have hL : play (n + 2) (LegibleBot (2*k+64) k) (GuardianBot k) = some .C :=
    eval_mono_le hn (n + 2) (by omega)
  have hG : play (n + 2) (GuardianBot k) (LegibleBot (2*k+64) k) = some .C :=
    lg_guardian_C_vs_legible k n hgf
  exact ⟨n + 2, outcome_of_plays _ _ _ _ _ hL hG⟩

end PD.Theorems
