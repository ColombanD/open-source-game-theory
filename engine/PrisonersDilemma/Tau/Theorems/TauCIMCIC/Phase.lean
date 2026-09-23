import PrisonersDilemma.Tau.Theorems.Columns
import PrisonersDilemma.Tau.Theorems.TauDIMCID.Helpers
import PrisonersDilemma.Tau.Theorems.TauMirror.Helpers
import PrisonersDilemma.Tau.RowSpec
import PrisonersDilemma.Outcome.Attr

/-!
# τ(CIMCIC)'s phase — the conditional cooperator: the first `.impl`-guard row.

C exactly where its consequent — "the partner's instance cooperates with me" — is
CERTIFIABLE: the constant cooperator, both TFTs, the mutual-Löb Dupoc cell (the
first entangled cell closed by COOPERATION), Just (through the same Löb bit), and
itself (the `implRefl` diagonal — after subst its guard is literally `φ → φ`).
Everywhere else the consequent is false or floor-priced and it defects — notably
against ALL FOUR floor bots (EBot's cascade, Guardian's and CupodTroll's else-play
trust, Cupod's entangled trust) and against DBot and OBot: a prover-tier bot pays
the prover-tier price on every Gödelian cell at once.

Boundary `θ ≤ cimcicMass`, Löb-gated through the entangled dupoc slot.
-/

open PD PD.BaseTheorems

namespace PD.Tau

/-- τ(CIMCIC)'s bit ROW. -/
def cimcicRow : Tmpl → Action
  | .coop     => .C
  | .tftSim   => .C
  | .tftPf    => .C
  | .dupoc    => .C
  | .just     => .C
  | .cimcic   => .C
  | .dimcid   => .D
  -- the cimcic×mirror entangled cell, Löb-gated below
  | .prudent  => .D
  | .mirror   => .C
  | .maxconfidence => .C
  | .minconfidence => .C
  | _         => .D

/-- The row's witness: one `weakenImpl`/census verdict per hypothesis; the
    entangled dupoc slot is the mutual-Löb play, supplied as a hypothesis (the
    `∃k₂` gate). -/
theorem cimcicRow_plays {k : Nat} (hL : 100 * Nat.log2 k + 1000 ≤ k)
    (hcg : c_guard k + 20 ≤ k)
    (hcq : proofSearch k (probe (inst (tauZoo k) .cimcic .dupoc)) = true)
    (hmdP : ∃ N, eval N (.bot (inst (tauZoo k) .cimcic .dupoc))
      (.bot (inst (tauZoo k) .cimcic .dupoc)) (inst (tauZoo k) .cimcic .dupoc)
      = some (cimcicRow .dupoc))
    (hmirP : ∃ N, eval N (.bot (inst (tauZoo k) .cimcic .mirror))
      (.bot (inst (tauZoo k) .cimcic .mirror)) (inst (tauZoo k) .cimcic .mirror)
      = some (cimcicRow .mirror)) :
    ∀ T, ∃ N, eval N (.bot (inst (tauZoo k) .cimcic T)) (.bot (inst (tauZoo k) .cimcic T))
              (inst (tauZoo k) .cimcic T) = some (cimcicRow T)
  | .coop       => cimcic_coop_plays_C hL
  | .defect     => cimcic_defect_plays_D
  | .tftSim     => cimcic_tftSim_plays_C hL hcg
  | .tftPf      => cimcic_tftPf_plays_C hL hcg
  | .dupoc      => hmdP
  | .prudent    => cimcic_prudent_plays_D
  | .mirror     => hmirP
  | .ebot       => cimcic_ebot_plays_D
  | .just       => cimcic_just_plays_C hL hcq
  | .obot       => cimcic_obot_plays_D
  | .guardian   => cimcic_guardian_plays_D
  | .dbot       => cimcic_dbot_plays_D
  | .cupodTroll => cimcic_cupodTroll_plays_D
  | .cupod      => cimcic_cupod_plays_D
  | .cimcic     => cimcic_quine_plays_C hL
  | .dimcid     => cimcic_dimcid_plays_D
  | .maxconfidence => by
      rw [inst_at_maxconfidence_eq_dupoc k .cimcic (by decide) (by decide) (by decide)]
      exact hmdP
  | .minconfidence => by
      rw [inst_at_minconfidence_eq_dupoc k .cimcic (by decide) (by decide) (by decide)]
      exact hmdP

/-- **τ(CIMCIC)'s row** — the matrix-facing statement (`@[tau_row]`: validated by
    `Tau/Lint.lean`, exported to the app): unconditional at large `k`, the floors and
    Löb gates discharged inside. The former literal `VoteBits` list is `RowSpec.bits`. -/
@[tau_row]
theorem cimcicRowSpec : RowSpec .cimcic tauOrder cimcicRow := by
  obtain ⟨kM, hkM⟩ := ps_probe_inst_cimcic_dupoc
  obtain ⟨kP, hkP⟩ := cimcic_dupoc_plays_C
  obtain ⟨kA, hkA⟩ := linear_log2_add_le 100 1000
  obtain ⟨kX, hkX⟩ := cimcic_mirror_plays_C
  refine ⟨max (max kM kP) (max kA kX), fun k hk T _ => ?_⟩
  have hcq := hkM k (by omega)
  have hmdP := hkP k (by omega)
  have hL : 100 * Nat.log2 k + 1000 ≤ k := hkA k (by omega)
  have hmirP := hkX k (by omega)
  have hcg : c_guard k + 20 ≤ k := by
    have := Nat.log2_le_self k
    simp only [c_guard, numCost]; omega
  exact cimcicRow_plays hL hcg hcq hmdP hmirP T

/-- **τ(CIMCIC)** — boundary `θ ≤ cimcicMass`. UNCONDITIONAL since 2026-08-24:
    both entangled slots (dupoc, mirror) are closed by bounded Löb. -/
theorem tauCIMCIC_phase :
    ∃ k₂, ∀ k, k₂ < k →
      ∀ θ (w : Tmpl → Nat) (opponent : Prog),
      (θ ≤ cimcicMass w → ∃ N, play N (TauBotZ k .cimcic w θ) opponent = some .C)
      ∧ (¬ θ ≤ cimcicMass w → ∃ N, play N (TauBotZ k .cimcic w θ) opponent = some .D) := by
  obtain ⟨kM, hkM⟩ := ps_probe_inst_cimcic_dupoc
  obtain ⟨kP, hkP⟩ := cimcic_dupoc_plays_C
  obtain ⟨kA, hkA⟩ := linear_log2_add_le 100 1000
  obtain ⟨kX, hkX⟩ := cimcic_mirror_plays_C
  refine ⟨max (max kM kP) (max kA kX), fun k hk θ w opponent => ?_⟩
  have hcq := hkM k (by omega)
  have hmdP := hkP k (by omega)
  have hL : 100 * Nat.log2 k + 1000 ≤ k := hkA k (by omega)
  have hmirP := hkX k (by omega)
  have hcg : c_guard k + 20 ≤ k := by
    have := Nat.log2_le_self k
    simp only [c_guard, numCost]; omega
  have h := phase_of_bits (tauZoo k) .cimcic w cimcicRow tauOrder θ opponent
    (fun T _ => cimcicRow_plays hL hcg hcq hmdP hmirP T)
  simp only [bitMass, tauOrder, List.map, cimcicRow, massOf, massOf_ifC, massOf_ifD,
    TauBotZ] at h ⊢
  simpa [cimcicMass] using h

end PD.Tau
