import PrisonersDilemma.Tau.Theorems.Columns

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
  | .mirror     => searchProbe_plays_C _ _ (bC .mirror)

/-- The scanner-facing bit row (read by `app`'s `def4_theorems.py` — keep the
    literal list): `vecOf_bits`' mapped row, by defeq on the concrete zoo. -/
theorem tftPfBits {k : Nat} (hk : 2 ≤ k) (hkk : c_guard k + 3 ≤ k) (h6 : 6 ≤ k)
    (h10 : 10 ≤ k) (hL : 100 * Nat.log2 k + 1000 ≤ k) (hcg : c_guard k + 20 ≤ k) (w : Tmpl → Nat) :
    VoteBits (vecOf (tauZoo k) .tftPf w tauOrder)
      [(w .coop, .C), (w .defect, .D), (w .tftSim, .C), (w .tftPf, .C),
       (w .dupoc, .C), (w .ebot, .D), (w .just, .C), (w .obot, .C),
       (w .guardian, .D), (w .dbot, .D), (w .cupodTroll, .D), (w .cupod, .D), (w .cimcic, .C), (w .dimcid, .D), (w .mirror, .C)] :=
  vecOf_bits (tauZoo k) .tftPf w tftPfRow tauOrder
    fun T _ => tftPfRow_plays hk hkk h6 h10 hL hcg T

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
