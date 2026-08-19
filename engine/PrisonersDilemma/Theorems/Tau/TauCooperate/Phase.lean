import PrisonersDilemma.Theorems.Tau.Columns

/-!
# τ(CooperateBot)'s phase — signal-blind: its whole mass cooperates.
-/

open PD PD.BaseTheorems

namespace PD.Tau

theorem coopBits (k : Nat) (w : Tmpl → Nat) :
    VoteBits (vecOf (zoo6 k) .coop w order6)
      [(w .coop, .C), (w .defect, .C), (w .tftSim, .C),
       (w .tftPf, .C), (w .dupoc, .C), (w .ebot, .C)] :=
  .cons ⟨1, rfl⟩ (.cons ⟨1, rfl⟩ (.cons ⟨1, rfl⟩ (.cons ⟨1, rfl⟩
    (.cons ⟨1, rfl⟩ (.cons ⟨1, rfl⟩ .nil)))))

/-- **τ(CooperateBot)**: signal-blind — its whole mass cooperates. -/
theorem tauCooperate_phase (k : Nat) (w : Tmpl → Nat) (θ : Nat) (opponent : Prog) :
    (θ ≤ w .coop + (w .defect + (w .tftSim + (w .tftPf + (w .dupoc + (w .ebot + 0))))) →
      ∃ N, play N (TauBotZ k .coop w θ) opponent = some .C)
    ∧ (¬ θ ≤ w .coop + (w .defect + (w .tftSim + (w .tftPf + (w .dupoc + (w .ebot + 0))))) →
      ∃ N, play N (TauBotZ k .coop w θ) opponent = some .D) := by
  have h := tauPlayer_phase_bits θ (coopBits k w) opponent
  simpa [massOf, TauBotZ] using h

end PD.Tau
