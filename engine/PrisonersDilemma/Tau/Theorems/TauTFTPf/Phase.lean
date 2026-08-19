import PrisonersDilemma.Tau.Theorems.Columns

/-!
# τ(TitForTatBot), prover variant — the δ_C column read by PROOF.

Boundary `θ ≤ pfMass` — EXCLUDING `w .guardian` (Guardian's cooperation is
floor-priced, invisible to proof search): strictly below the behavioral twin's
`simMass` whenever `w .guardian > 0`.
-/

open PD PD.BaseTheorems

namespace PD.Tau

theorem tftPfBits {k : Nat} (hk : 2 ≤ k) (hkk : c_guard k + 3 ≤ k) (h6 : 6 ≤ k)
    (h10 : 10 ≤ k) (w : Tmpl → Nat) :
    VoteBits (vecOf (tauZoo k) .tftPf w tauOrder)
      [(w .coop, .C), (w .defect, .D), (w .tftSim, .C), (w .tftPf, .C),
       (w .dupoc, .C), (w .ebot, .D), (w .just, .C), (w .obot, .C),
       (w .guardian, .D)] :=
  let bC := ps_probe_inst_coop hk hkk h6 h10
  .cons (searchProbe_plays_C _ _ (bC .coop))
    (.cons (searchProbe_plays_D _ _ (bC .defect))
      (.cons (searchProbe_plays_C _ _ (bC .tftSim))
        (.cons (searchProbe_plays_C _ _ (bC .tftPf))
          (.cons (searchProbe_plays_C _ _ (bC .dupoc))
            (.cons (searchProbe_plays_D _ _ (bC .ebot))
              (.cons (searchProbe_plays_C _ _ (bC .just))
                (.cons (searchProbe_plays_C _ _ (bC .obot))
                  (.cons (searchProbe_plays_D _ _ (bC .guardian)) .nil))))))))

/-- **τ(TitForTatBot), prover** — boundary `θ ≤ pfMass` (Guardian excluded). -/
theorem tauTFTPf_phase {k : Nat} (hk : 2 ≤ k) (hkk : c_guard k + 3 ≤ k) (h6 : 6 ≤ k)
    (h10 : 10 ≤ k) (θ : Nat) (w : Tmpl → Nat) (opponent : Prog) :
    (θ ≤ pfMass w → ∃ N, play N (TauBotZ k .tftPf w θ) opponent = some .C)
    ∧ (¬ θ ≤ pfMass w → ∃ N, play N (TauBotZ k .tftPf w θ) opponent = some .D) := by
  have h := tauPlayer_phase_bits θ (tftPfBits hk hkk h6 h10 w) opponent
  simp only [massOf, massOf_ifC, massOf_ifD, TauBotZ] at h ⊢
  simpa [pfMass] using h

end PD.Tau
