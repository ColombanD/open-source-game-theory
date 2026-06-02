import PrisonersDilemma.Program
import PrisonersDilemma.Dynamics
import PrisonersDilemma.Axioms
import PrisonersDilemma.Bots.DupocBot
import PrisonersDilemma.Bots.TitForTatBot
import PrisonersDilemma.Bots.CooperateBot
import PrisonersDilemma.Theorems.ProofSearch
import PrisonersDilemma.Theorems.Helpers

open PDNew
open PDNew.Axioms
open PDNew.Bots
namespace PDNew.Theorems

theorem llm_outcome_DupocBot_vs_TitForTatBot (n : Nat) :
    ∃ k, outcome (n+4) (DupocBot k) TitForTatBot = some (.C, .C) := by
  have hCB0 : ∃ m, play m (.bot CooperateBot) (DupocBot 0) = some .C := ⟨2, rfl⟩
  obtain ⟨w₀, hw₀⟩ := witness_complete_plays (.bot CooperateBot) (DupocBot 0) .C hCB0
  let s₀ : Nat := witnessChars w₀

  have hCB_for : ∀ k, s₀ ≤ k →
      proofSearch k (.plays (.bot CooperateBot) (DupocBot k) .C) = true := by
    intro k hk
    obtain ⟨w', hw', hwk'⟩ :=
      witness_transport_family
        (fun i => .plays (.bot CooperateBot) (DupocBot i) .C)
        0 k (Nat.zero_le _) w₀ hw₀ hk
    exact (proofSearch_spec k _).2 ⟨w', hw', hwk'⟩

  have hTFT_at : ∀ k, s₀ ≤ k → ∀ m,
      play (m+4) TitForTatBot (DupocBot k) = some .C := by
    intro k hk m
    have hps := hCB_for k hk
    show eval (m+4) TitForTatBot (DupocBot k) TitForTatBot = some .C
    unfold TitForTatBot DupocBot at hps ⊢
    simp [eval, Prog.subst, Formula.subst, hps]
    rfl

  have hTFT_s0 : ∃ m, play m TitForTatBot (DupocBot s₀) = some .C :=
    ⟨0+4, hTFT_at s₀ (Nat.le_refl _) 0⟩
  obtain ⟨w₁, hw₁⟩ := witness_complete_plays TitForTatBot (DupocBot s₀) .C hTFT_s0
  let s₁ : Nat := witnessChars w₁

  let k : Nat := max s₀ s₁
  refine ⟨k, ?_⟩
  have hk0 : s₀ ≤ k := Nat.le_max_left s₀ s₁
  have hk1 : s₁ ≤ k := Nat.le_max_right s₀ s₁

  have hB : play (n+4) TitForTatBot (DupocBot k) = some .C := hTFT_at k hk0 n

  have hPS_TFT : proofSearch k (.plays TitForTatBot (DupocBot k) .C) = true := by
    obtain ⟨w', hw', hwk'⟩ :=
      witness_transport_family
        (fun i => .plays TitForTatBot (DupocBot i) .C)
        s₀ k hk0 w₁ hw₁ hk1
    exact (proofSearch_spec k _).2 ⟨w', hw', hwk'⟩

  have hA : play (n+4) (DupocBot k) TitForTatBot = some .C := by
    show eval (n+4) (DupocBot k) TitForTatBot (DupocBot k) = some .C
    unfold DupocBot at hPS_TFT ⊢
    simp [eval, Prog.subst, Formula.subst, hPS_TFT]

  exact outcome_of_plays _ _ _ _ _ hA hB

end PDNew.Theorems
