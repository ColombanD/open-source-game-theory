import PrisonersDilemma.Tau.Theorems.Columns
import PrisonersDilemma.Tau.RowSpec
import PrisonersDilemma.Outcome.Attr

/-!
# τ(TitForTatBot), prover variant — the δ_C column read by PROOF.

Boundary `θ ≤ pfMass` — EXCLUDING `w .guardian` (Guardian's cooperation is
floor-priced, invisible to proof search): strictly below the behavioral twin's
`simMass` whenever `w .guardian > 0`.
-/

open PD PD.BaseTheorems

namespace PD.Tau

/-- τ(TFTPf)'s bit ROW: the prover δ_C column — Guardian's floor-priced C reads
    as D. -/
def tftPfRow : Tmpl → Action
  | .coop     => .C
  | .defect   => .D
  | .tftSim   => .C
  | .tftPf    => .C
  | .dupoc    => .C
  | .ebot     => .D
  | .just     => .C
  | .obot     => .C
  | .guardian => .D
  | .dbot     => .D
  | .cupod      => .D
  | .cupodTroll => .D
  | .cimcic     => .C
  | .dimcid     => .D
  | .prudent    => .D
  | .mirror     => .C

/-- The row's witness: every entry is a prove-stage on the δ_C prover column. -/
theorem tftPfRow_plays {k : Nat} (hk : 2 ≤ k) (hkk : c_guard k + 3 ≤ k) (h6 : 6 ≤ k)
    (h10 : 10 ≤ k) (hL : 100 * Nat.log2 k + 1000 ≤ k) (hcg : c_guard k + 20 ≤ k) :
    ∀ T, ∃ N, eval N (.bot (inst (tauZoo k) .tftPf T)) (.bot (inst (tauZoo k) .tftPf T))
              (inst (tauZoo k) .tftPf T) = some (tftPfRow T) :=
  let bC := ps_probe_inst_coop hk hkk h6 h10 hL hcg
  fun T => match T with
  | .coop     => searchProbe_plays_C _ _ (bC .coop)
  | .defect   => searchProbe_plays_D _ _ (bC .defect)
  | .tftSim   => searchProbe_plays_C _ _ (bC .tftSim)
  | .tftPf    => searchProbe_plays_C _ _ (bC .tftPf)
  | .dupoc    => searchProbe_plays_C _ _ (bC .dupoc)
  | .ebot     => searchProbe_plays_D _ _ (bC .ebot)
  | .just     => searchProbe_plays_C _ _ (bC .just)
  | .obot     => searchProbe_plays_C _ _ (bC .obot)
  | .guardian => searchProbe_plays_D _ _ (bC .guardian)
  | .dbot     => searchProbe_plays_D _ _ (bC .dbot)
  | .cupod      => searchProbe_plays_D _ _ (bC .cupod)
  | .cupodTroll => searchProbe_plays_D _ _ (bC .cupodTroll)
  | .cimcic     => searchProbe_plays_C _ _ (bC .cimcic)
  | .dimcid     => searchProbe_plays_D _ _ (bC .dimcid)
  | .prudent    => searchProbe_plays_D _ _ (bC .prudent)
  | .mirror     => searchProbe_plays_C _ _ (bC .mirror)

/-- **τ(TFTPf)'s row** — the matrix-facing statement (`@[tau_row]`: validated by
    `Tau/Lint.lean`, exported to the app): unconditional at large `k`, the floors and
    Löb gates discharged inside. The former literal `VoteBits` list is `RowSpec.bits`. -/
@[tau_row]
theorem tftPfRowSpec : RowSpec .tftPf tauOrder tftPfRow := by
  obtain ⟨K, hK⟩ := linear_log2_add_le 100 1000
  refine ⟨K + 10, fun k hk T _ => ?_⟩
  have hL : 100 * Nat.log2 k + 1000 ≤ k := hK k (by omega)
  have := Nat.log2_le_self k
  exact tftPfRow_plays (by omega) (by simp only [c_guard, numCost]; omega) (by omega) (by omega) hL
    (by simp only [c_guard, numCost]; omega) T

/-- **τ(TitForTatBot), prover** — boundary `θ ≤ pfMass` (Guardian excluded). -/
theorem tauTFTPf_phase {k : Nat} (hk : 2 ≤ k) (hkk : c_guard k + 3 ≤ k) (h6 : 6 ≤ k)
    (h10 : 10 ≤ k) (hL : 100 * Nat.log2 k + 1000 ≤ k) (hcg : c_guard k + 20 ≤ k) (θ : Nat) (w : Tmpl → Nat) (opponent : Prog) :
    (θ ≤ pfMass w → ∃ N, play N (TauBotZ k .tftPf w θ) opponent = some .C)
    ∧ (¬ θ ≤ pfMass w → ∃ N, play N (TauBotZ k .tftPf w θ) opponent = some .D) := by
  have h := phase_of_bits (tauZoo k) .tftPf w tftPfRow tauOrder θ opponent
    (fun T _ => tftPfRow_plays hk hkk h6 h10 hL hcg T)
  simp only [bitMass, tauOrder, List.map, tftPfRow, massOf, massOf_ifC, massOf_ifD,
    TauBotZ] at h ⊢
  simpa [pfMass] using h

end PD.Tau
