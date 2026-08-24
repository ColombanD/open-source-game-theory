import PrisonersDilemma.Tau.Theorems.Columns

/-!
# τ(DefectBot)'s phase — zero cooperation mass; defects at every θ ≠ 0.
-/

open PD PD.BaseTheorems

namespace PD.Tau

/-- τ(DefectBot)'s bit ROW: signal-blind defection. -/
def defectRow : Tmpl → Action := fun _ => .D

/-- The row's witness: every instance is the compiled constant `.const .D`. -/
theorem defectRow_plays (k : Nat) :
    ∀ T, ∃ N, eval N (.bot (inst (tauZoo k) .defect T)) (.bot (inst (tauZoo k) .defect T))
              (inst (tauZoo k) .defect T) = some (defectRow T) := by
  intro T; cases T <;> exact ⟨1, rfl⟩

/-- The scanner-facing bit row (read by `app`'s `def4_theorems.py` — keep the
    literal list): `vecOf_bits`' mapped row, by defeq on the concrete zoo. -/
theorem defectBits (k : Nat) (w : Tmpl → Nat) :
    VoteBits (vecOf (tauZoo k) .defect w tauOrder)
      [(w .coop, .D), (w .defect, .D), (w .tftSim, .D), (w .tftPf, .D),
       (w .dupoc, .D), (w .ebot, .D), (w .just, .D), (w .obot, .D),
       (w .guardian, .D), (w .dbot, .D), (w .cupodTroll, .D), (w .cupod, .D), (w .cimcic, .D), (w .dimcid, .D), (w .mirror, .D)] :=
  vecOf_bits (tauZoo k) .defect w defectRow tauOrder fun T _ => defectRow_plays k T

/-- **τ(DefectBot)**: zero mass — cooperates only at θ = 0. -/
theorem tauDefect_phase (k : Nat) (w : Tmpl → Nat) (θ : Nat) (opponent : Prog) :
    (θ = 0 → ∃ N, play N (TauBotZ k .defect w θ) opponent = some .C)
    ∧ (θ ≠ 0 → ∃ N, play N (TauBotZ k .defect w θ) opponent = some .D) := by
  have h := phase_of_bits (tauZoo k) .defect w defectRow tauOrder θ opponent
    (fun T _ => defectRow_plays k T)
  simp only [bitMass, tauOrder, List.map, defectRow, massOf, massOf_ifD, TauBotZ]
    at h ⊢
  exact ⟨fun hθ => h.1 (by omega), fun hθ => h.2 (by omega)⟩

end PD.Tau
