import PrisonersDilemma.Tau.Theorems.Columns

/-!
# τ(TitForTatBot), behavioral variant — the δ_C column read by SIMULATION.
Boundary `θ ≤ coopMass`, reached at a far smaller budget than the prover twin:
the prover/behavioral split is a budget gap, not an α gap.
-/

open PD PD.BaseTheorems

namespace PD.Tau

theorem tftSimBits {k : Nat} (hk : 2 ≤ k) (hkk : c_guard k + 3 ≤ k) (h6 : 6 ≤ k)
    (w : Tmpl → Nat) :
    VoteBits (vecOf (zoo6 k) .tftSim w order6)
      [(w .coop, .C), (w .defect, .D), (w .tftSim, .C),
       (w .tftPf, .C), (w .dupoc, .C), (w .ebot, .D)] :=
  -- τ(TFTSim)'s entry at T COPIES T's δ_C-column TRUE play: the behavioral column.
  let pC := inst_coop_plays hk hkk h6
  .cons (simCopy_plays _ _ (pC .coop))
    (.cons (simCopy_plays _ _ (pC .defect))
      (.cons (simCopy_plays _ _ (pC .tftSim))
        (.cons (simCopy_plays _ _ (pC .tftPf))
          (.cons (simCopy_plays _ _ (pC .dupoc))
            (.cons (simCopy_plays _ _ (pC .ebot)) .nil)))))

/-- **τ(TitForTatBot), behavioral variant** — same boundary, far smaller budget. -/
theorem tauTFTSim_phase {k : Nat} (hk : 2 ≤ k) (hkk : c_guard k + 3 ≤ k) (h6 : 6 ≤ k)
    (θ : Nat) (w : Tmpl → Nat) (opponent : Prog) :
    (θ ≤ w .coop + (w .tftSim + (w .tftPf + w .dupoc)) →
      ∃ N, play N (TauBotZ k .tftSim w θ) opponent = some .C)
    ∧ (¬ θ ≤ w .coop + (w .tftSim + (w .tftPf + w .dupoc)) →
      ∃ N, play N (TauBotZ k .tftSim w θ) opponent = some .D) := by
  have h := tauPlayer_phase_bits θ (tftSimBits hk hkk h6 w) opponent
  simp only [massOf, massOf_ifC, massOf_ifD, TauBotZ] at h ⊢
  simpa using h

end PD.Tau
