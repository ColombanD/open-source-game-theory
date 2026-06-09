import PrisonersDilemma.Bots.CupodBot
import PrisonersDilemma.Dynamics
import PrisonersDilemma.Axioms
import PrisonersDilemma.Theorems.ProofSearch

open PD
open PD.Axioms
open PD.Bots

namespace PD.Theorems

theorem llm_outcome_CupodBot_vs_CupodBot :
    ∃ k, ∀ n, outcome (n + 2) (CupodBot k) (CupodBot k) = some (.D, .D) := by
  let Φ : Nat → Formula := fun k =>
    Formula.plays (CupodBot k) (CupodBot k) Action.D
  have hPBLT : ∃ k₂, ∀ k, k > k₂ → ∃ m, proofSearch m (Φ k) = true := by
    apply PBLT Φ id 0
    · intros a b hab; exact hab
    · refine ⟨1, 0, by omega, ?_⟩
      intros k hk
      show k > 1 * Nat.log2 k
      have hk0 : k ≠ 0 := by omega
      have hlog : Nat.log2 k < k := by
        rw [Nat.log2_lt hk0]
        exact Nat.lt_pow_self (by omega : 1 < 2)
      omega
    · intros k _
      have hbot : CupodBot k =
          .search k (.plays .opp .self Action.D)
            (.const Action.D) (.const Action.C) := rfl
      have hax := proof_system_verifies_search_branch k
        (.plays .opp .self Action.D) Action.D Action.C
        (CupodBot k) (CupodBot k) hbot
      simpa [Φ, Formula.subst, Prog.subst, id] using hax
  obtain ⟨k₂, hk₂⟩ := hPBLT
  have h := hk₂ (k₂ + 1) (Nat.lt_succ_self k₂)
  obtain ⟨m, hm⟩ := h
  obtain ⟨w, hw, hwsize⟩ := (proofSearch_spec m (Φ (k₂ + 1))).1 hm
  let k : Nat := max (k₂ + 1) (witnessChars w)
  have hk1 : k₂ + 1 ≤ k := Nat.le_max_left _ _
  have hkw : witnessChars w ≤ k := Nat.le_max_right _ _
  obtain ⟨w', hw', hw'size⟩ := witness_transport_family Φ (k₂ + 1) k hk1 w hw hkw
  have hps : proofSearch k (Φ k) = true :=
    (proofSearch_spec k (Φ k)).2 ⟨w', hw', hw'size⟩
  refine ⟨k, ?_⟩
  intro n
  have hplay : play (n + 2) (CupodBot k) (CupodBot k) = some .D := by
    show eval (n + 2) (CupodBot k) (CupodBot k) (CupodBot k) = some .D
    unfold CupodBot
    show (if proofSearch k
              ((Formula.plays Prog.opp Prog.self Action.D).subst
                (CupodBot k) (CupodBot k)) = true
          then eval (n + 1) (CupodBot k) (CupodBot k) (.const Action.D)
          else eval (n + 1) (CupodBot k) (CupodBot k) (.const Action.C))
        = some Action.D
    have heq : (Formula.plays Prog.opp Prog.self Action.D).subst
                (CupodBot k) (CupodBot k) = Φ k := by
      simp [Φ, Formula.subst, Prog.subst]
    rw [heq, hps]
    simp [eval]
  simp [outcome, hplay]

end PD.Theorems
