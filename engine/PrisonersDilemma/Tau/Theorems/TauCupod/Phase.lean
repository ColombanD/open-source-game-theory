import PrisonersDilemma.Tau.Theorems.Columns
import PrisonersDilemma.Tau.Theorems.TauMirror.Helpers
import PrisonersDilemma.Tau.Theorems.TauDIMCID.Helpers
import PrisonersDilemma.Tau.RowSpec
import PrisonersDilemma.Outcome.Attr

/-!
# τ(CupodBot)'s phase — the suspicious cooperator, Löb-gated TWICE over.

Cupod trusts by default and punishes only what it can convict. On this zoo it
convicts exactly the defector and ITSELF (`ps_probeD_inst_cupod_quine` — the
polarity-inverted Löb quine), so its boundary is `θ ≤ cupodMass` = everything but
those two weights.

One gate remains: the DIAGONAL bit is the Löb threshold (like Dupoc's quine — the
`∃k₂` gate). The formerly-open entangled `.dupoc` slot is now a THEOREM
(`cupod_dupoc_plays_C` — the floor closure, `TauCupod/Helpers`), with exactly the
value that used to be its canonical hypothesis: the tau image of the base red cell
`outcome_DupocBot_vs_CupodBot = (D, C)`. The `.cimcic` slot is a theorem too
(`cupod_cimcic_plays_C`): the suspicious cooperator trusts the conditional
cooperator it cannot convict.
-/

open PD PD.BaseTheorems

namespace PD.Tau

/-- τ(Cupod)'s bit ROW: it punishes exactly the two it can convict — the constant
    defector and ITSELF. -/
def cupodRow : Tmpl → Action
  | .defect     => .D
  | .cupod      => .D
  -- RESTATED 2026-08-24: with `proveEq` fixed, τ(CupodTroll) recognises Cupod
  -- and defects on it — so Cupod convicts the troll in turn.
  | .cupodTroll => .D
  | .prudent    => .C
  | .mirror     => .D
  -- the ALIGNED entangled pair: mutual Löb on DEFECTION (see `TauDIMCID`)
  | .dimcid     => .D
  | _           => .C

/-- The row's witness: one punish-probe per hypothesis, fed the δ_Cu guard column;
    the diagonal is the Löb quine, the `.dupoc` slot the open entangled play. -/
theorem cupodRow_plays {k : Nat} (hk : 2 ≤ k) (hkk : c_guard k + 3 ≤ k) (h6 : 6 ≤ k)
    (h10 : 10 ≤ k)
    (hquine : proofSearch k (probeD (inst (tauZoo k) .cupod .cupod)) = true)
    -- the mirror×cupod entangled cell (mutual simulation), Löb-gated
    (hmirCu : proofSearch k (probeD (inst (tauZoo k) .mirror .cupod))
      = cupodColBit .mirror)
    (hmirP : ∃ N, eval N (.bot (inst (tauZoo k) .cupod .mirror))
      (.bot (inst (tauZoo k) .cupod .mirror)) (inst (tauZoo k) .cupod .mirror)
      = some (cupodRow .mirror))
    -- the ALIGNED dimcid pair: mutual Löb on defection, gated like the diagonal
    (hdc : proofSearch k (probeD (inst (tauZoo k) .dimcid .cupod))
      = cupodColBit .dimcid)
    (hdcP : ∃ N, eval N (.bot (inst (tauZoo k) .cupod .dimcid))
      (.bot (inst (tauZoo k) .cupod .dimcid)) (inst (tauZoo k) .cupod .dimcid)
      = some Action.D) :
    ∀ T, ∃ N, eval N (.bot (inst (tauZoo k) .cupod T)) (.bot (inst (tauZoo k) .cupod T))
              (inst (tauZoo k) .cupod T) = some (cupodRow T) :=
  let bCu := ps_probeD_inst_cupod hk hkk hquine hdc hmirCu
  fun T => match T with
  | .coop       => searchProbeD_plays_C _ _ (bCu .coop)
  | .defect     => searchProbeD_plays_D _ _ (bCu .defect)
  | .tftSim     => searchProbeD_plays_C _ _ (bCu .tftSim)
  | .tftPf      => searchProbeD_plays_C _ _ (bCu .tftPf)
  | .dupoc      => cupod_dupoc_plays_C
  | .ebot       => searchProbeD_plays_C _ _ (bCu .ebot)
  | .just       => searchProbeD_plays_C _ _ (bCu .just)
  | .obot       => searchProbeD_plays_C _ _ (bCu .obot)
  | .guardian   => searchProbeD_plays_C _ _ (bCu .guardian)
  | .dbot       => searchProbeD_plays_C _ _ (bCu .dbot)
  | .cupodTroll => searchProbeD_plays_D _ _ (bCu .cupodTroll)
  | .cupod      => inst_cupod_quine_plays_D hquine
  | .cimcic     => cupod_cimcic_plays_C
  | .prudent    => cupod_prudent_plays_C   -- it cannot convict Prudent: the D is an else-play
  | .mirror     => hmirP
  | .dimcid     => hdcP

/-- **τ(Cupod)'s row** — the matrix-facing statement (`@[tau_row]`: validated by
    `Tau/Lint.lean`, exported to the app): unconditional at large `k`, the floors and
    Löb gates discharged inside. The former literal `VoteBits` list is `RowSpec.bits`. -/
@[tau_row]
theorem cupodRowSpec : RowSpec .cupod tauOrder cupodRow := by
  obtain ⟨kL, hkL⟩ := ps_probeD_inst_cupod_quine
  obtain ⟨kA, hkA⟩ := linear_log2_add_le 1 12
  obtain ⟨kX, hkX⟩ := ps_probeD_mirror_cupod
  obtain ⟨kY, hkY⟩ := cupod_mirror_plays_D
  obtain ⟨kD, hkD⟩ := ps_probeD_inst_dimcid_cupod
  obtain ⟨kE, hkE⟩ := cupod_dimcid_plays_D
  refine ⟨max (max kL kA) (max (max kX kY) (max kD kE)), fun k hk T _ => ?_⟩
  have hdc := hkD k (by omega)
  have hdcP := hkE k (by omega)
  have hquine := hkL k (by omega)
  have hkA' : 1 * Nat.log2 k + 12 ≤ k := hkA k (by omega)
  have hmirCu := hkX k (by omega)
  have hmirP := hkY k (by omega)
  have hk2 : 2 ≤ k := by omega
  have hkk : c_guard k + 3 ≤ k := by simp only [c_guard, numCost]; omega
  have h6 : 6 ≤ k := by omega
  have h10 : 10 ≤ k := by omega
  exact cupodRow_plays hk2 hkk h6 h10 hquine hmirCu hmirP hdc hdcP T

/-- **τ(CupodBot)** — boundary `θ ≤ cupodMass`. UNCONDITIONAL since 2026-08-24:
    its diagonal is the punish-polarity quine, its mirror slot a Löb fixpoint on
    defection (`TauMirror/Helpers`), and its dimcid slot the first ALIGNED-on-D
    pair, closed by mutual bounded Löb (`TauDIMCID/Helpers`). -/
theorem tauCupod_phase :
    ∃ k₂, ∀ k, k₂ < k →
      ∀ θ (w : Tmpl → Nat) (opponent : Prog),
      (θ ≤ cupodMass w → ∃ N, play N (TauBotZ k .cupod w θ) opponent = some .C)
      ∧ (¬ θ ≤ cupodMass w → ∃ N, play N (TauBotZ k .cupod w θ) opponent = some .D) := by
  obtain ⟨kL, hkL⟩ := ps_probeD_inst_cupod_quine
  obtain ⟨kA, hkA⟩ := linear_log2_add_le 1 12
  obtain ⟨kX, hkX⟩ := ps_probeD_mirror_cupod
  obtain ⟨kY, hkY⟩ := cupod_mirror_plays_D
  obtain ⟨kD, hkD⟩ := ps_probeD_inst_dimcid_cupod
  obtain ⟨kE, hkE⟩ := cupod_dimcid_plays_D
  refine ⟨max (max kL kA) (max (max kX kY) (max kD kE)), fun k hk θ w opponent => ?_⟩
  have hdc := hkD k (by omega)
  have hdcP := hkE k (by omega)
  have hquine := hkL k (by omega)
  have hkA' : 1 * Nat.log2 k + 12 ≤ k := hkA k (by omega)
  have hmirCu := hkX k (by omega)
  have hmirP := hkY k (by omega)
  have hk2 : 2 ≤ k := by omega
  have hkk : c_guard k + 3 ≤ k := by simp only [c_guard, numCost]; omega
  have h6 : 6 ≤ k := by omega
  have h10 : 10 ≤ k := by omega
  have h := phase_of_bits (tauZoo k) .cupod w cupodRow tauOrder θ opponent
    (fun T _ => cupodRow_plays hk2 hkk h6 h10 hquine hmirCu hmirP hdc hdcP T)
  simp only [bitMass, tauOrder, List.map, cupodRow, massOf, massOf_ifC, massOf_ifD,
    TauBotZ] at h ⊢
  simpa [cupodMass] using h

end PD.Tau
