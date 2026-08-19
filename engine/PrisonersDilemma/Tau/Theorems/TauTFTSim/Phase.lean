import PrisonersDilemma.Tau.Theorems.Columns

/-!
# τ(TitForTatBot), behavioral variant — the δ_C column read by SIMULATION.

Boundary `θ ≤ simMass` — which INCLUDES `w .guardian`: the behavioral read sees
Guardian's floor-priced cooperation that no prover can cite. With Guardian in the
zoo the prover/behavioral split is an α-GAP (`pfMass < simMass`), not just a budget
gap — the band `pfMass < θ ≤ simMass` separates this bot from its prover twin.
-/

open PD PD.BaseTheorems

namespace PD.Tau

theorem tftSimBits {k : Nat} (hk : 2 ≤ k) (hkk : c_guard k + 3 ≤ k) (h6 : 6 ≤ k)
    (h10 : 10 ≤ k) (w : Tmpl → Nat) :
    VoteBits (vecOf (tauZoo k) .tftSim w tauOrder)
      [(w .coop, .C), (w .defect, .D), (w .tftSim, .C), (w .tftPf, .C),
       (w .dupoc, .C), (w .ebot, .D), (w .just, .C), (w .obot, .C),
       (w .guardian, .C)] :=
  let pC := inst_coop_plays hk hkk h6 h10
  .cons (simCopy_plays _ _ (pC .coop))
    (.cons (simCopy_plays _ _ (pC .defect))
      (.cons (simCopy_plays _ _ (pC .tftSim))
        (.cons (simCopy_plays _ _ (pC .tftPf))
          (.cons (simCopy_plays _ _ (pC .dupoc))
            (.cons (simCopy_plays _ _ (pC .ebot))
              (.cons (simCopy_plays _ _ (pC .just))
                (.cons (simCopy_plays _ _ (pC .obot))
                  (.cons (simCopy_plays _ _ (pC .guardian)) .nil))))))))

/-- **τ(TitForTatBot), behavioral** — boundary `θ ≤ simMass` (incl. Guardian). -/
theorem tauTFTSim_phase {k : Nat} (hk : 2 ≤ k) (hkk : c_guard k + 3 ≤ k) (h6 : 6 ≤ k)
    (h10 : 10 ≤ k) (θ : Nat) (w : Tmpl → Nat) (opponent : Prog) :
    (θ ≤ simMass w → ∃ N, play N (TauBotZ k .tftSim w θ) opponent = some .C)
    ∧ (¬ θ ≤ simMass w → ∃ N, play N (TauBotZ k .tftSim w θ) opponent = some .D) := by
  have h := tauPlayer_phase_bits θ (tftSimBits hk hkk h6 h10 w) opponent
  simp only [massOf, massOf_ifC, massOf_ifD, TauBotZ] at h ⊢
  simpa [simMass] using h

end PD.Tau
