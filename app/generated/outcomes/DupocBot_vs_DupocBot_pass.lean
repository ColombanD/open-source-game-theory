import PrisonersDilemma.Bots.DupocBot
import PrisonersDilemma.Axioms
import PrisonersDilemma.Theorems.ProofSearch

open PDNew
open PDNew.Axioms
open PDNew.Bots

namespace PDNew.Theorems

private theorem dupoc_loeb_premise (k : Nat) :
    ∃ m, proofSearch m
      (.impl (.box k (.plays (DupocBot k) (DupocBot k) .C))
             (.plays (DupocBot k) (DupocBot k) .C)) = true := by
  have h := proof_system_verifies_search_branch
              k (.plays .opp .self .C) .C .D
              (DupocBot k) (DupocBot k) rfl
  simpa [Formula.subst, Prog.subst] using h

theorem llm_outcome_DupocBot_vs_DupocBot :
    ∃ k₂, ∀ k, k₂ < k →
      ∃ fuel, outcome fuel (DupocBot k) (DupocBot k) = some (.C, .C) := by
  let φ : Nat → Formula := fun k => .plays (DupocBot k) (DupocBot k) .C
  have hMono : ∀ a b : Nat, a ≤ b → id a ≤ id b := fun _ _ h => h
  have hLog : ∃ c kHat, c > 0 ∧ ∀ k, k > kHat → id k > c * Nat.log2 k := by
    refine ⟨1, 0, Nat.zero_lt_one, ?_⟩
    intro k hk
    have hlog : Nat.log2 k < k := by
      rw [Nat.log2_lt (Nat.pos_iff_ne_zero.mp hk)]
      exact Nat.lt_two_pow_self
    simpa using hlog
  have hLoeb :
      ∀ k, k > 0 →
        ∃ m, proofSearch m (.impl (.box (id k) (φ k)) (φ k)) = true := by
    intro k _
    simpa using dupoc_loeb_premise k
  obtain ⟨k₂, hk₂⟩ := PBLT φ id 0 hMono hLog hLoeb
  refine ⟨k₂, ?_⟩
  intro k hk
  obtain ⟨m, hm⟩ := hk₂ k hk
  have hInterp : (φ k).interp := proofSearch_sound m (φ k) hm
  obtain ⟨n, hn⟩ := hInterp
  refine ⟨n, ?_⟩
  simp [outcome, hn]

end PDNew.Theorems
