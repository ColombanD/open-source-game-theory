import PrisonersDilemma.Theorems.Tau.Columns

/-!
# τ(TitForTatBot), prover variant — the δ_C column read by PROOF.
Boundary `θ ≤ coopMass`.
-/

open PD PD.BaseTheorems

namespace PD.Tau

theorem tftPfBits {k : Nat} (hk : 2 ≤ k) (hkk : c_guard k + 3 ≤ k) (h6 : 6 ≤ k)
    (w : Tmpl → Nat) :
    VoteBits (vecOf (zoo6 k) .tftPf w order6)
      [(w .coop, .C), (w .defect, .D), (w .tftSim, .C),
       (w .tftPf, .C), (w .dupoc, .C), (w .ebot, .D)] :=
  -- τ(TFTPf)'s entry at T probes T's δ_C column bit: ONE column read.
  let bC := ps_probe_inst_coop hk hkk h6
  .cons (searchProbe_plays_C _ _ (bC .coop))
    (.cons (searchProbe_plays_D _ _ (bC .defect))
      (.cons (searchProbe_plays_C _ _ (bC .tftSim))
        (.cons (searchProbe_plays_C _ _ (bC .tftPf))
          (.cons (searchProbe_plays_C _ _ (bC .dupoc))
            (.cons (searchProbe_plays_D _ _ (bC .ebot)) .nil)))))

/-- **τ(TitForTatBot), prover variant.** -/
theorem tauTFTPf_phase {k : Nat} (hk : 2 ≤ k) (hkk : c_guard k + 3 ≤ k) (h6 : 6 ≤ k)
    (θ : Nat) (w : Tmpl → Nat) (opponent : Prog) :
    (θ ≤ w .coop + (w .tftSim + (w .tftPf + w .dupoc)) →
      ∃ N, play N (TauBotZ k .tftPf w θ) opponent = some .C)
    ∧ (¬ θ ≤ w .coop + (w .tftSim + (w .tftPf + w .dupoc)) →
      ∃ N, play N (TauBotZ k .tftPf w θ) opponent = some .D) := by
  have h := tauPlayer_phase_bits θ (tftPfBits hk hkk h6 w) opponent
  simp only [massOf, massOf_ifC, massOf_ifD, TauBotZ] at h ⊢
  simpa using h

end PD.Tau
