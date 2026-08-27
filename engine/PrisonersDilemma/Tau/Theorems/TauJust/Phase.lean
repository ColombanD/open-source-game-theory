import PrisonersDilemma.Tau.Theorems.Columns
import PrisonersDilemma.Tau.Theorems.TauMirror.Helpers
import PrisonersDilemma.Tau.RowSpec
import PrisonersDilemma.Outcome.Attr

/-!
# τ(JustBot)'s phase — Löb-GATED, like TauDupoc's, and with the SAME boundary.

JustBot thresholds the same δ_L column Dupoc does (by name instead of by self), so
its bit row and boundary `θ ≤ dupMass` coincide with Dupoc's — including inheriting
the Löb gate: its Dupoc entry probes THE QUINE. Norm-based and self-based
reciprocity are behaviorally indistinguishable on this zoo at large k.
-/

open PD PD.BaseTheorems

namespace PD.Tau

/-- τ(JustBot)'s bit ROW: the prover δ_L column, read by NAME — identical to
    `dupocRow`. -/
def justRow : Tmpl → Action
  | .coop     => .C
  | .defect   => .D
  | .tftSim   => .C
  | .tftPf    => .C
  | .dupoc    => .C
  | .ebot     => .D
  | .just     => .C
  | .obot     => .D
  | .guardian => .D
  | .dbot     => .D
  | .cupod      => .D
  | .cupodTroll => .D
  | .cimcic     => .C
  | .dimcid     => .D
  | .prudent    => .D
  | .confidence => .C
  | .mirror     => .C

/-- The row's witness: prove-stages on the δ_L column — including at the `.dupoc`
    slot, where the probed object is the quine (by name, not by self). -/
theorem justRow_plays {k : Nat} (hk : 2 ≤ k) (hkk : c_guard k + 3 ≤ k)
    (hk7 : c_guard k + 7 ≤ k)
    (hquine : proofSearch k (probe (inst (tauZoo k) .dupoc .dupoc)) = true)
    (hcim : proofSearch k (probe (inst (tauZoo k) .cimcic .dupoc)) = dupocColBit .cimcic)
    -- the mirror×dupoc entangled bit, read through the same δ_L column
    (hmir : proofSearch k (probe (inst (tauZoo k) .mirror .dupoc))
      = dupocColBit .mirror)
    -- the confidence×dupoc system's Löb bit, read through the same column
    (hconf : proofSearch k (probe (inst (tauZoo k) .confidence .dupoc))
      = dupocColBit .confidence) :
    ∀ T, ∃ N, eval N (.bot (inst (tauZoo k) .just T)) (.bot (inst (tauZoo k) .just T))
              (inst (tauZoo k) .just T) = some (justRow T) :=
  let bL := ps_probe_inst_dupoc hk hkk hk7 hquine hcim hmir hconf
  fun T => match T with
  | .coop     => searchProbe_plays_C _ _ (bL .coop)
  | .defect   => searchProbe_plays_D _ _ (bL .defect)
  | .tftSim   => searchProbe_plays_C _ _ (bL .tftSim)
  | .tftPf    => searchProbe_plays_C _ _ (bL .tftPf)
  | .dupoc    => searchProbe_plays_C _ _ (bL .dupoc)
  | .ebot     => searchProbe_plays_D _ _ (bL .ebot)
  | .just     => searchProbe_plays_C _ _ (bL .just)
  | .obot     => searchProbe_plays_D _ _ (bL .obot)
  | .guardian => searchProbe_plays_D _ _ (bL .guardian)
  | .dbot     => searchProbe_plays_D _ _ (bL .dbot)
  | .cupod      => searchProbe_plays_D _ _ (bL .cupod)
  | .cupodTroll => searchProbe_plays_D _ _ (bL .cupodTroll)
  | .cimcic     => searchProbe_plays_C _ _ (bL .cimcic)
  | .dimcid     => searchProbe_plays_D _ _ (bL .dimcid)
  | .prudent    => searchProbe_plays_D _ _ (bL .prudent)
  | .mirror     => searchProbe_plays_C _ _ (bL .mirror)
  | .confidence => searchProbe_plays_C _ _ (bL .confidence)

/-- **τ(Just)'s row** — the matrix-facing statement (`@[tau_row]`: validated by
    `Tau/Lint.lean`, exported to the app): unconditional at large `k`, the floors and
    Löb gates discharged inside. The former literal `VoteBits` list is `RowSpec.bits`. -/
@[tau_row]
theorem justRowSpec : RowSpec .just tauOrder justRow := by
  obtain ⟨kL, hkL⟩ := ps_probe_inst_quine
  obtain ⟨kA, hkA⟩ := linear_log2_add_le 1 8
  obtain ⟨kM, hkM⟩ := ps_probe_inst_cimcic_dupoc
  obtain ⟨kX, hkX⟩ := ps_probe_mirror_dupoc
  obtain ⟨kC, hkC⟩ := ps_probe_inst_confidence_dupoc
  refine ⟨kL + kA + kM + kX + kC, fun k hk T _ => ?_⟩
  have hquine := hkL k (by omega)
  have hkA' : 1 * Nat.log2 k + 8 ≤ k := hkA k (by omega)
  have hcim := hkM k (by omega)
  have hmir := hkX k (by omega)
  have hconf := hkC k (by omega)
  have hk2 : 2 ≤ k := by omega
  have hkk : c_guard k + 3 ≤ k := by simp only [c_guard, numCost]; omega
  have hk7 : c_guard k + 7 ≤ k := by simp only [c_guard, numCost]; omega
  exact justRow_plays hk2 hkk hk7 hquine hcim hmir hconf T

/-- **τ(JustBot)** — boundary `θ ≤ dupMass`, same as TauDupoc's. UNCONDITIONAL
    since 2026-08-24: the mirror×dupoc bit it reads is a theorem. -/
theorem tauJust_phase :
    ∃ k₂, ∀ k, k₂ < k →
      ∀ θ (w : Tmpl → Nat) (opponent : Prog),
      (θ ≤ dupMass w → ∃ N, play N (TauBotZ k .just w θ) opponent = some .C)
      ∧ (¬ θ ≤ dupMass w → ∃ N, play N (TauBotZ k .just w θ) opponent = some .D) := by
  obtain ⟨kL, hkL⟩ := ps_probe_inst_quine
  obtain ⟨kA, hkA⟩ := linear_log2_add_le 1 8
  obtain ⟨kM, hkM⟩ := ps_probe_inst_cimcic_dupoc
  obtain ⟨kX, hkX⟩ := ps_probe_mirror_dupoc
  obtain ⟨kC, hkC⟩ := ps_probe_inst_confidence_dupoc
  refine ⟨kL + kA + kM + kX + kC, fun k hk θ w opponent => ?_⟩
  have hquine := hkL k (by omega)
  have hkA' : 1 * Nat.log2 k + 8 ≤ k := hkA k (by omega)
  have hcim := hkM k (by omega)
  have hmir := hkX k (by omega)
  have hconf := hkC k (by omega)
  have hk2 : 2 ≤ k := by omega
  have hkk : c_guard k + 3 ≤ k := by simp only [c_guard, numCost]; omega
  have hk7 : c_guard k + 7 ≤ k := by simp only [c_guard, numCost]; omega
  have h := phase_of_bits (tauZoo k) .just w justRow tauOrder θ opponent
    (fun T _ => justRow_plays hk2 hkk hk7 hquine hcim hmir hconf T)
  simp only [bitMass, tauOrder, List.map, justRow, massOf, massOf_ifC, massOf_ifD,
    TauBotZ] at h ⊢
  simpa [dupMass] using h

end PD.Tau
