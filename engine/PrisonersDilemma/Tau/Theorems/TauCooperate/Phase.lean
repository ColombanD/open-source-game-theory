import PrisonersDilemma.Tau.Theorems.Columns
import PrisonersDilemma.Tau.RowSpec
import PrisonersDilemma.Outcome.Attr

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

/-- **τ(Cooperate)'s row** — the matrix-facing statement (`@[tau_row]`: validated by
    `Tau/Lint.lean`, exported to the app): unconditional at large `k`, the floors and
    Löb gates discharged inside. The former literal `VoteBits` list is `RowSpec.bits`. -/
@[tau_row]
theorem coopRowSpec : RowSpec .coop tauOrder coopRow := ⟨0, fun k _ T _ => coopRow_plays k T⟩

/-- **τ(CooperateBot)**: cooperates at every θ within the total mass. -/
theorem tauCooperate_phase (k : Nat) (w : Tmpl → Nat) (θ : Nat) (opponent : Prog) :
    (θ ≤ w .coop + (w .defect + (w .tftSim + (w .tftPf + (w .dupoc + (w .ebot +
        (w .just + (w .obot + (w .guardian + (w .dbot + (w .cupodTroll + (w .cupod + (w .cimcic + (w .dimcid + (w .prudent + (w .maxconfidence + (w .minconfidence + w .mirror)))))))))))))))) →
      ∃ N, play N (TauBotZ k .coop w θ) opponent = some .C)
    ∧ (¬ θ ≤ w .coop + (w .defect + (w .tftSim + (w .tftPf + (w .dupoc + (w .ebot +
        (w .just + (w .obot + (w .guardian + (w .dbot + (w .cupodTroll + (w .cupod + (w .cimcic + (w .dimcid + (w .prudent + (w .maxconfidence + (w .minconfidence + w .mirror)))))))))))))))) →
      ∃ N, play N (TauBotZ k .coop w θ) opponent = some .D) := by
  have h := phase_of_bits (tauZoo k) .coop w coopRow tauOrder θ opponent
    (fun T _ => coopRow_plays k T)
  simp only [bitMass, tauOrder, List.map, coopRow, massOf, massOf_ifC, TauBotZ]
    at h ⊢
  simpa [-forall_const] using h

end PD.Tau
