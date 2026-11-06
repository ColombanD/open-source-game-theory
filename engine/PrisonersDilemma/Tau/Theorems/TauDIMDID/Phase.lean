import PrisonersDilemma.Tau.Theorems.TauDIMDID.Helpers
import PrisonersDilemma.Tau.Theorems.TauDIMDID.Loeb
import PrisonersDilemma.Tau.Theorems.TauDIMDID.Tower
import PrisonersDilemma.Tau.RowSpec
import PrisonersDilemma.Outcome.Attr

/-!
# τ(DIMDID)'s phase — τ(CIMCIC)'s row, transposed (2026-10-19)

`D` against the constant defector, Cupod (τ̂ of the `cimcic × dupoc` mutual Löb), DIMCID (the
aligned-on-D pair), the mirror and itself; `C` everywhere else — the else-play.
-/

open PD PD.BaseTheorems

namespace PD.Tau

def dimdidRow : Tmpl → Action
  | .coop       => .C
  | .defect     => .D
  | .tftSim     => .C
  | .tftPf      => .C
  | .dupoc      => .C
  | .ebot       => .C
  | .just       => .C
  | .obot       => .C
  | .guardian   => .C
  | .dbot       => .C
  | .cupodTroll => .C
  | .dupocTroll => .C
  | .cupod      => .D
  | .cimcic     => .C
  | .dimcid     => .D
  | .dimdid     => .D
  | .prudent    => .C
  | .maxconfidence => .C
  | .minconfidence => .C
  | .mirror     => .D

/-- The display form of the C-mass. -/
def dimdidMass (w : Tmpl → Nat) : Nat :=
  w .coop + w .tftSim + w .tftPf + w .dupoc + w .ebot + w .just + w .obot + w .guardian
    + w .dbot + w .cupodTroll + w .cimcic + w .prudent + w .maxconfidence + w .minconfidence
    + w .dupocTroll

theorem dimdidRow_plays :
    ∃ k₂, ∀ k, k₂ < k → ∀ T,
      ∃ N, eval N (.bot (inst (tauZoo k) .dimdid T)) (.bot (inst (tauZoo k) .dimdid T))
        (inst (tauZoo k) .dimdid T) = some (dimdidRow T) := by
  obtain ⟨kA, hkA⟩ := linear_log2_add_le 100 1000
  obtain ⟨k1, h1⟩ := dimdid_cupod_plays_D
  obtain ⟨k2, h2⟩ := dimdid_mirror_plays_D
  obtain ⟨k4, h4⟩ := dimdid_dimcid_plays_D
  refine ⟨max kA (max k1 (max k2 k4)), fun k hk T => ?_⟩
  have hL : 100 * Nat.log2 k + 1000 ≤ k := hkA k (by omega)
  cases T with
  | coop => exact dimdid_coop_plays_C
  | defect => exact dimdid_defect_plays_D hL
  | tftSim => exact dimdid_tftSim_plays_C
  | tftPf => exact dimdid_tftPf_plays_C
  | dupoc => exact dimdid_dupoc_plays_C
  | ebot => exact dimdid_ebot_plays_C hL
  | just => exact dimdid_just_plays_C
  | obot => exact dimdid_obot_plays_C
  | guardian => exact dimdid_guardian_plays_C
  | dbot => exact dimdid_dbot_plays_C hL
  | cupodTroll => exact dimdid_cupodTroll_plays_C
  | dupocTroll => exact dimdid_dupocTroll_plays_C
  | cupod => exact h1 k (by omega)
  | cimcic => exact dimdid_cimcic_plays_C
  | dimcid => exact h4 k (by omega)
  | dimdid => exact dimdid_dimdid_plays_D hL
  | prudent => exact dimdid_prudent_plays_C
  | maxconfidence =>
      rw [inst_at_maxconfidence_eq_dupoc k .dimdid (by decide) (by decide) (by decide)]
      exact dimdid_dupoc_plays_C
  | minconfidence =>
      rw [inst_at_minconfidence_eq_dupoc k .dimdid (by decide) (by decide) (by decide)]
      exact dimdid_dupoc_plays_C
  | mirror => exact h2 k (by omega)

/-- **τ(DIMDID)'s row** — the matrix-facing statement (`@[tau_row]`: validated by
    `Tau/Lint.lean`, exported to the app): unconditional at large `k`. -/
@[tau_row]
theorem dimdidRowSpec : RowSpec .dimdid tauOrder dimdidRow := by
  obtain ⟨k₂, h⟩ := dimdidRow_plays
  exact ⟨k₂, fun k hk T _ => h k hk T⟩

set_option maxHeartbeats 1600000 in
/-- **τ(DIMDID)'s phase** — boundary `θ ≤ dimdidMass`. Unconditional. -/
theorem tauDIMDID_phase :
    ∃ k₂, ∀ k, k₂ < k →
      ∀ θ (w : Tmpl → Nat) (opponent : Prog),
      (θ ≤ dimdidMass w → ∃ N, play N (TauBotZ k .dimdid w θ) opponent = some .C)
      ∧ (¬ θ ≤ dimdidMass w → ∃ N, play N (TauBotZ k .dimdid w θ) opponent = some .D) := by
  obtain ⟨k₂, hrow⟩ := dimdidRow_plays
  refine ⟨k₂, fun k hk θ w opponent => ?_⟩
  have h := phase_of_bits (tauZoo k) .dimdid w dimdidRow tauOrder θ opponent
    (fun T _ => hrow k hk T)
  simp only [bitMass, tauOrder, List.map, dimdidRow, massOf, massOf_ifC, massOf_ifD] at h
  exact ⟨fun hθ => h.1 (by unfold dimdidMass at hθ; omega),
         fun hθ => h.2 (by unfold dimdidMass at hθ; omega)⟩

end PD.Tau
