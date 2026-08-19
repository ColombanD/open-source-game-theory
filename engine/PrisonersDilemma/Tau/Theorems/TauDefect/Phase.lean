import PrisonersDilemma.Tau.Theorems.Columns

/-!
# τ(DefectBot)'s phase — zero cooperation mass; defects at every θ ≠ 0.
-/

open PD PD.BaseTheorems

namespace PD.Tau

theorem defectBits (k : Nat) (w : Tmpl → Nat) :
    VoteBits (vecOf (tauZoo k) .defect w tauOrder)
      [(w .coop, .D), (w .defect, .D), (w .tftSim, .D), (w .tftPf, .D),
       (w .dupoc, .D), (w .ebot, .D), (w .just, .D), (w .obot, .D),
       (w .guardian, .D)] :=
  .cons ⟨1, rfl⟩ (.cons ⟨1, rfl⟩ (.cons ⟨1, rfl⟩ (.cons ⟨1, rfl⟩ (.cons ⟨1, rfl⟩
    (.cons ⟨1, rfl⟩ (.cons ⟨1, rfl⟩ (.cons ⟨1, rfl⟩ (.cons ⟨1, rfl⟩ .nil))))))))

/-- **τ(DefectBot)**: zero mass — cooperates only at θ = 0. -/
theorem tauDefect_phase (k : Nat) (w : Tmpl → Nat) (θ : Nat) (opponent : Prog) :
    (θ = 0 → ∃ N, play N (TauBotZ k .defect w θ) opponent = some .C)
    ∧ (θ ≠ 0 → ∃ N, play N (TauBotZ k .defect w θ) opponent = some .D) := by
  have h := tauPlayer_phase_bits θ (defectBits k w) opponent
  simp only [massOf, massOf_ifD, TauBotZ] at h ⊢
  exact ⟨fun hθ => h.1 (by omega), fun hθ => h.2 (by omega)⟩

end PD.Tau
