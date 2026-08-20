import PrisonersDilemma.Tau.Theorems.Columns

/-!
# τ(CooperateBot)'s phase — signal-blind: its whole mass cooperates.
-/

open PD PD.BaseTheorems

namespace PD.Tau

/-- τ(CooperateBot)'s bit ROW: what its instance plays at each hypothesis —
    signal-blind cooperation. -/
def coopRow : Tmpl → Action := fun _ => .C

/-- The row's witness: every instance is the compiled constant `.const .C`. -/
theorem coopRow_plays (k : Nat) :
    ∀ T, ∃ N, eval N (.bot (inst (tauZoo k) .coop T)) (.bot (inst (tauZoo k) .coop T))
              (inst (tauZoo k) .coop T) = some (coopRow T) := by
  intro T; cases T <;> exact ⟨1, rfl⟩

/-- The scanner-facing bit row (read by `app`'s `def4_theorems.py` — keep the
    literal list): `vecOf_bits`' mapped row, by defeq on the concrete zoo. -/
theorem coopBits (k : Nat) (w : Tmpl → Nat) :
    VoteBits (vecOf (tauZoo k) .coop w tauOrder)
      [(w .coop, .C), (w .defect, .C), (w .tftSim, .C), (w .tftPf, .C),
       (w .dupoc, .C), (w .ebot, .C), (w .just, .C), (w .obot, .C),
       (w .guardian, .C), (w .dbot, .C), (w .cupodTroll, .C)] :=
  vecOf_bits (tauZoo k) .coop w coopRow tauOrder fun T _ => coopRow_plays k T

/-- **τ(CooperateBot)**: cooperates at every θ within the total mass. -/
theorem tauCooperate_phase (k : Nat) (w : Tmpl → Nat) (θ : Nat) (opponent : Prog) :
    (θ ≤ w .coop + (w .defect + (w .tftSim + (w .tftPf + (w .dupoc + (w .ebot +
        (w .just + (w .obot + (w .guardian + (w .dbot + w .cupodTroll))))))))) →
      ∃ N, play N (TauBotZ k .coop w θ) opponent = some .C)
    ∧ (¬ θ ≤ w .coop + (w .defect + (w .tftSim + (w .tftPf + (w .dupoc + (w .ebot +
        (w .just + (w .obot + (w .guardian + (w .dbot + w .cupodTroll))))))))) →
      ∃ N, play N (TauBotZ k .coop w θ) opponent = some .D) := by
  have h := phase_of_bits (tauZoo k) .coop w coopRow tauOrder θ opponent
    (fun T _ => coopRow_plays k T)
  simp only [bitMass, tauOrder, List.map, coopRow, massOf, massOf_ifC, TauBotZ]
    at h ⊢
  simpa using h

end PD.Tau
