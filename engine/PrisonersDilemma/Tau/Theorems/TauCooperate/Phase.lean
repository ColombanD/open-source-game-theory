import PrisonersDilemma.Tau.Theorems.Columns

/-!
# τ(CooperateBot)'s phase — signal-blind: its whole mass cooperates.
-/

open PD PD.BaseTheorems

namespace PD.Tau

theorem coopBits (k : Nat) (w : Tmpl → Nat) :
    VoteBits (vecOf (tauZoo k) .coop w tauOrder)
      [(w .coop, .C), (w .defect, .C), (w .tftSim, .C), (w .tftPf, .C),
       (w .dupoc, .C), (w .ebot, .C), (w .just, .C), (w .obot, .C),
       (w .guardian, .C)] :=
  .cons ⟨1, rfl⟩ (.cons ⟨1, rfl⟩ (.cons ⟨1, rfl⟩ (.cons ⟨1, rfl⟩ (.cons ⟨1, rfl⟩
    (.cons ⟨1, rfl⟩ (.cons ⟨1, rfl⟩ (.cons ⟨1, rfl⟩ (.cons ⟨1, rfl⟩ .nil))))))))

/-- **τ(CooperateBot)**: cooperates at every θ within the total mass. -/
theorem tauCooperate_phase (k : Nat) (w : Tmpl → Nat) (θ : Nat) (opponent : Prog) :
    (θ ≤ w .coop + (w .defect + (w .tftSim + (w .tftPf + (w .dupoc + (w .ebot +
        (w .just + (w .obot + w .guardian))))))) →
      ∃ N, play N (TauBotZ k .coop w θ) opponent = some .C)
    ∧ (¬ θ ≤ w .coop + (w .defect + (w .tftSim + (w .tftPf + (w .dupoc + (w .ebot +
        (w .just + (w .obot + w .guardian))))))) →
      ∃ N, play N (TauBotZ k .coop w θ) opponent = some .D) := by
  have h := tauPlayer_phase_bits θ (coopBits k w) opponent
  simp only [massOf, massOf_ifC, massOf_ifD, TauBotZ] at h ⊢
  simpa using h

end PD.Tau
