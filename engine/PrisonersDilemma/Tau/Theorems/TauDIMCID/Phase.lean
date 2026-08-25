import PrisonersDilemma.Tau.Theorems.TauDIMCID.Helpers
import PrisonersDilemma.Tau.Theorems.TauPrudent.Helpers
import PrisonersDilemma.Tau.Theorems.TauMirror.Helpers

/-!
# τ(DIMCID)'s phase — the last row (2026-08-25)

Every slot is a theorem. The row is DIMCID's own play at each hypothesis:
`D` against the constant defector, against Cupod (the aligned-on-D pair, mutual
Löb), against the mirror (Löb on its guard through the forwarder) and against
itself (the Löb fixpoint on defection); `C` everywhere else — the else-play, by
seven different censuses, the last two of which (`guardian`, `cupodTroll`) needed
the tower census (`Base/TowerCensus.lean`).
-/

open PD PD.BaseTheorems

namespace PD.Tau

def dimcidRow : Tmpl → Action
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
  | .cupod      => .D
  | .cimcic     => .C
  | .dimcid     => .D
  | .prudent    => .C
  | .mirror     => .D

/-- The display form of the C-mass. -/
def dimcidMass (w : Tmpl → Nat) : Nat :=
  w .coop + w .tftSim + w .tftPf + w .dupoc + w .ebot + w .just + w .obot + w .guardian
    + w .dbot + w .cupodTroll + w .cimcic + w .prudent

theorem dimcidRow_plays :
    ∃ k₂, ∀ k, k₂ < k → ∀ T,
      ∃ N, eval N (.bot (inst (tauZoo k) .dimcid T)) (.bot (inst (tauZoo k) .dimcid T))
        (inst (tauZoo k) .dimcid T) = some (dimcidRow T) := by
  obtain ⟨kA, hkA⟩ := linear_log2_add_le 100 1000
  obtain ⟨k1, h1⟩ := dimcid_cupod_plays_D
  obtain ⟨k2, h2⟩ := dimcid_mirror_plays_D
  obtain ⟨k3, h3⟩ := dimcid_dimcid_plays_D
  refine ⟨max kA (max k1 (max k2 k3)), fun k hk T => ?_⟩
  have hL : 100 * Nat.log2 k + 1000 ≤ k := hkA k (by omega)
  cases T with
  | coop => exact dimcid_coop_plays_C
  | defect => exact dimcid_defect_plays_D hL
  | tftSim => exact dimcid_tftSim_plays_C
  | tftPf => exact dimcid_tftPf_plays_C
  | dupoc => exact dimcid_dupoc_plays_C
  | ebot => exact dimcid_ebot_plays_C hL
  | just => exact dimcid_just_plays_C
  | obot => exact dimcid_obot_plays_C
  | guardian => exact dimcid_guardian_plays_C
  | dbot => exact dimcid_dbot_plays_C hL
  | cupodTroll => exact dimcid_cupodTroll_plays_C
  | cupod => exact h1 k (by omega)
  | cimcic => exact dimcid_cimcic_plays_C
  | dimcid => exact h3 k (by omega)
  | prudent => exact dimcid_prudent_plays_C
  | mirror => exact h2 k (by omega)

/-- The scanner-facing bit row (read by `app`'s `def4_theorems.py` — keep the
    literal list). -/
theorem dimcidBits :
    ∃ k₂, ∀ k, k₂ < k → ∀ (w : Tmpl → Nat),
      VoteBits (vecOf (tauZoo k) .dimcid w tauOrder)
        [(w .coop, .C), (w .defect, .D), (w .tftSim, .C), (w .tftPf, .C),
         (w .dupoc, .C), (w .ebot, .C), (w .just, .C), (w .obot, .C),
         (w .guardian, .C), (w .dbot, .C), (w .cupodTroll, .C), (w .cupod, .D), (w .cimcic, .C), (w .dimcid, .D), (w .prudent, .C), (w .mirror, .D)] := by
  obtain ⟨k₂, hrow⟩ := dimcidRow_plays
  exact ⟨k₂, fun k hk w => vecOf_bits (tauZoo k) .dimcid w dimcidRow tauOrder (fun T _ => hrow k hk T)⟩

/-- **τ(DIMCID)'s phase** — boundary `θ ≤ dimcidMass`. Unconditional. -/
theorem tauDIMCID_phase :
    ∃ k₂, ∀ k, k₂ < k →
      ∀ θ (w : Tmpl → Nat) (opponent : Prog),
      (θ ≤ dimcidMass w → ∃ N, play N (TauBotZ k .dimcid w θ) opponent = some .C)
      ∧ (¬ θ ≤ dimcidMass w → ∃ N, play N (TauBotZ k .dimcid w θ) opponent = some .D) := by
  obtain ⟨k₂, hrow⟩ := dimcidRow_plays
  refine ⟨k₂, fun k hk θ w opponent => ?_⟩
  have h := phase_of_bits (tauZoo k) .dimcid w dimcidRow tauOrder θ opponent
    (fun T _ => hrow k hk T)
  simp only [bitMass, tauOrder, List.map, dimcidRow, massOf, massOf_ifC, massOf_ifD,
    TauBotZ] at h
  exact ⟨fun hθ => h.1 (by unfold dimcidMass at hθ; omega),
         fun hθ => h.2 (by unfold dimcidMass at hθ; omega)⟩

end PD.Tau
