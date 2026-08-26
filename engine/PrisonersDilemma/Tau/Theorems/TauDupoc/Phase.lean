import PrisonersDilemma.Tau.Theorems.Columns
import PrisonersDilemma.Tau.Theorems.TauMirror.Helpers
import PrisonersDilemma.Tau.RowSpec
import PrisonersDilemma.Outcome.Attr

/-!
# τ(DupocBot)'s phase — Löb-GATED: its diagonal bit is the quine.

Boundary `θ ≤ dupMass` — excluding `w .ebot` and `w .guardian` (both floors) and
`w .obot` (a true defection: OBot's second watch catches Dupoc defecting against
the defector).
-/

open PD PD.BaseTheorems

namespace PD.Tau

/-- τ(DupocBot)'s bit ROW: the prover δ_L column, with the QUINE on the
    diagonal. -/
def dupocRow : Tmpl → Action
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
  | .mirror     => .C

/-- The row's witness: prove-stages on the δ_L column; the diagonal is the Löb
    quine, supplied as a hypothesis. -/
theorem dupocRow_plays {k : Nat} (hk : 2 ≤ k) (hkk : c_guard k + 3 ≤ k)
    (hk7 : c_guard k + 7 ≤ k)
    (hquine : proofSearch k (probe (inst (tauZoo k) .dupoc .dupoc)) = true)
    (hcim : proofSearch k (probe (inst (tauZoo k) .cimcic .dupoc)) = dupocColBit .cimcic)
    (hmir : proofSearch k (probe (inst (tauZoo k) .mirror .dupoc)) = dupocColBit .mirror)
    (hmirP : ∃ N, eval N (.bot (inst (tauZoo k) .dupoc .mirror))
      (.bot (inst (tauZoo k) .dupoc .mirror)) (inst (tauZoo k) .dupoc .mirror)
      = some (dupocRow .mirror))
    (hdmP : ∃ N, eval N (.bot (inst (tauZoo k) .dupoc .cimcic))
      (.bot (inst (tauZoo k) .dupoc .cimcic)) (inst (tauZoo k) .dupoc .cimcic)
      = some (dupocRow .cimcic)) :
    ∀ T, ∃ N, eval N (.bot (inst (tauZoo k) .dupoc T)) (.bot (inst (tauZoo k) .dupoc T))
              (inst (tauZoo k) .dupoc T) = some (dupocRow T) :=
  let bL := ps_probe_inst_dupoc hk hkk hk7 hquine hcim hmir
  fun T => match T with
  | .coop     => searchProbe_plays_C _ _ (bL .coop)
  | .defect   => searchProbe_plays_D _ _ (bL .defect)
  | .tftSim   => searchProbe_plays_C _ _ (bL .tftSim)
  | .tftPf    => searchProbe_plays_C _ _ (bL .tftPf)
  | .dupoc    => inst_quine_plays hquine
  | .ebot     => searchProbe_plays_D _ _ (bL .ebot)
  | .just     => searchProbe_plays_C _ _ (bL .just)
  | .obot     => searchProbe_plays_D _ _ (bL .obot)
  | .guardian => searchProbe_plays_D _ _ (bL .guardian)
  | .dbot     => searchProbe_plays_D _ _ (bL .dbot)
  | .cupod      => -- the entangled cell, CLOSED BY THE FLOOR (TauCupod/Helpers)
      dupoc_cupod_plays_D
  | .cupodTroll => searchProbe_plays_D _ _ (bL .cupodTroll)
  | .cimcic     => hdmP   -- the mutual-Löb cell (∃k₂-gated, TauCIMCIC/Helpers)
  | .prudent    => dupoc_prudent_plays_D   -- its probe of Prudent's member fails (D by soundness)
  | .mirror     => hmirP   -- the mirror×dupoc entangled cell (gated)
  | .dimcid     => -- the anti-aligned entangled pair, closed by the floor
      dupoc_dimcid_plays_D

/-- **τ(Dupoc)'s row** — the matrix-facing statement (`@[tau_row]`: validated by
    `Tau/Lint.lean`, exported to the app): unconditional at large `k`, the floors and
    Löb gates discharged inside. The former literal `VoteBits` list is `RowSpec.bits`. -/
@[tau_row]
theorem dupocRowSpec : RowSpec .dupoc tauOrder dupocRow := by
  obtain ⟨kL, hkL⟩ := ps_probe_inst_quine
  obtain ⟨kA, hkA⟩ := linear_log2_add_le 1 8
  obtain ⟨kM, hkM⟩ := ps_probe_inst_cimcic_dupoc
  obtain ⟨kP, hkP⟩ := dupoc_cimcic_plays_C
  obtain ⟨kX, hkX⟩ := ps_probe_mirror_dupoc
  obtain ⟨kY, hkY⟩ := dupoc_mirror_plays_C
  refine ⟨max (max kL kA) (max (max kM kP) (max kX kY)), fun k hk T _ => ?_⟩
  have hquine := hkL k (by omega)
  have hkA' : 1 * Nat.log2 k + 8 ≤ k := hkA k (by omega)
  have hcim := hkM k (by omega)
  have hdmP := hkP k (by omega)
  have hmir := hkX k (by omega)
  have hmirP := hkY k (by omega)
  have hk2 : 2 ≤ k := by omega
  have hkk : c_guard k + 3 ≤ k := by simp only [c_guard, numCost]; omega
  have hk7 : c_guard k + 7 ≤ k := by simp only [c_guard, numCost]; omega
  exact dupocRow_plays hk2 hkk hk7 hquine hcim hmir hmirP hdmP T

/-- **τ(DupocBot)** — boundary `θ ≤ dupMass`. UNCONDITIONAL: the mirror×dupoc
    entangled cell (a mutual SIMULATION — mirror forwards, dupoc proves — the tau
    image of base `outcome_DupocBot_vs_MirrorBot`) is closed by bounded Löb in
    `TauMirror/Helpers` (2026-08-24), so its bit and its play are supplied here,
    no longer assumed. -/
theorem tauDupoc_phase :
    ∃ k₂, ∀ k, k₂ < k →
      ∀ θ (w : Tmpl → Nat) (opponent : Prog),
      (θ ≤ dupMass w → ∃ N, play N (TauBotZ k .dupoc w θ) opponent = some .C)
      ∧ (¬ θ ≤ dupMass w → ∃ N, play N (TauBotZ k .dupoc w θ) opponent = some .D) := by
  obtain ⟨kL, hkL⟩ := ps_probe_inst_quine
  obtain ⟨kA, hkA⟩ := linear_log2_add_le 1 8
  obtain ⟨kM, hkM⟩ := ps_probe_inst_cimcic_dupoc
  obtain ⟨kP, hkP⟩ := dupoc_cimcic_plays_C
  obtain ⟨kX, hkX⟩ := ps_probe_mirror_dupoc
  obtain ⟨kY, hkY⟩ := dupoc_mirror_plays_C
  refine ⟨max (max kL kA) (max (max kM kP) (max kX kY)), fun k hk θ w opponent => ?_⟩
  have hquine := hkL k (by omega)
  have hkA' : 1 * Nat.log2 k + 8 ≤ k := hkA k (by omega)
  have hcim := hkM k (by omega)
  have hdmP := hkP k (by omega)
  have hmir := hkX k (by omega)
  have hmirP := hkY k (by omega)
  have hk2 : 2 ≤ k := by omega
  have hkk : c_guard k + 3 ≤ k := by simp only [c_guard, numCost]; omega
  have hk7 : c_guard k + 7 ≤ k := by simp only [c_guard, numCost]; omega
  have h := phase_of_bits (tauZoo k) .dupoc w dupocRow tauOrder θ opponent
    (fun T _ => dupocRow_plays hk2 hkk hk7 hquine hcim hmir hmirP hdmP T)
  simp only [bitMass, tauOrder, List.map, dupocRow, massOf, massOf_ifC, massOf_ifD,
    TauBotZ] at h ⊢
  simpa [dupMass] using h

end PD.Tau
