import PrisonersDilemma.Program
import PrisonersDilemma.Dynamics
import PrisonersDilemma.Axioms
import PrisonersDilemma.Bots.CooperateBot
import PrisonersDilemma.Bots.DupocBot
import PrisonersDilemma.Theorems.ProofSearch

open PDNew
open PDNew.Axioms
open PDNew.Bots
namespace PDNew.Theorems

/-- Monotonicity of DupocBot in `k`: transport a witness across parameter growth. -/
theorem DupocBot_monotonicity (Bot : Prog) (a : Action) (n k : Nat) :
    n ≤ k →
    proofSearch k (.plays Bot (DupocBot n) a) = true →
    proofSearch k (.plays Bot (DupocBot k) a) = true := by
  intro hle hnk
  let Φ : Nat → Formula := fun i => Formula.plays Bot (DupocBot i) a
  obtain ⟨w, hw, hwk⟩ := (proofSearch_spec k (Φ n)).1 hnk
  obtain ⟨w', hw', hwk'⟩ := witness_transport_family Φ n k hle w hw hwk
  exact (proofSearch_spec k (Φ k)).2 ⟨w', hw', hwk'⟩

/-- For some `k`, proofSearch verifies that CooperateBot plays C against DupocBot k. -/
theorem proofSearch_true_for_CB_vs_DupocBot :
    ∃ k, proofSearch k (.plays CooperateBot (DupocBot k) .C) = true := by
  have hex0 : ∃ m, play m CooperateBot (DupocBot 0) = some .C := ⟨1, rfl⟩
  obtain ⟨k₀, hk₀⟩ := proofSearch_complete_plays CooperateBot (DupocBot 0) .C hex0
  exact ⟨k₀, DupocBot_monotonicity CooperateBot .C 0 k₀ (Nat.zero_le _) hk₀⟩

theorem llm_outcome_CooperateBot_vs_DupocBot (n : Nat) :
    ∃ k, outcome (n+2) CooperateBot (DupocBot k) = some (.C, .C) := by
  obtain ⟨k, hk⟩ := proofSearch_true_for_CB_vs_DupocBot
  refine ⟨k, ?_⟩
  have hA : play (n+2) CooperateBot (DupocBot k) = some .C := rfl
  have hB : play (n+2) (DupocBot k) CooperateBot = some .C := by
    show eval (n+2) (DupocBot k) CooperateBot (DupocBot k) = some .C
    unfold DupocBot at hk ⊢
    simp [eval, Prog.subst, Formula.subst, hk]
  simp [outcome, hA, hB]

end PDNew.Theorems
