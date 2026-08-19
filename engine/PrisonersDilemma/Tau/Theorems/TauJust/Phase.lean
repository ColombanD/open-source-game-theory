import PrisonersDilemma.Tau.Theorems.Columns

/-!
# τ(JustBot)'s phase — Löb-GATED, like TauDupoc's, and with the SAME boundary.

JustBot thresholds the same δ_L column Dupoc does (by name instead of by self), so
its bit row and boundary `θ ≤ dupMass` coincide with Dupoc's — including inheriting
the Löb gate: its Dupoc entry probes THE QUINE. Norm-based and self-based
reciprocity are behaviorally indistinguishable on this zoo at large k.
-/

open PD PD.BaseTheorems

namespace PD.Tau

theorem justBits {k : Nat} (hk : 2 ≤ k) (hkk : c_guard k + 3 ≤ k)
    (hk7 : c_guard k + 7 ≤ k)
    (hquine : proofSearch k (probe (inst (tauZoo k) .dupoc .dupoc)) = true)
    (w : Tmpl → Nat) :
    VoteBits (vecOf (tauZoo k) .just w tauOrder)
      [(w .coop, .C), (w .defect, .D), (w .tftSim, .C), (w .tftPf, .C),
       (w .dupoc, .C), (w .ebot, .D), (w .just, .C), (w .obot, .D),
       (w .guardian, .D)] :=
  let bL := ps_probe_inst_dupoc hk hkk hk7 hquine
  .cons (searchProbe_plays_C _ _ (bL .coop))
    (.cons (searchProbe_plays_D _ _ (bL .defect))
      (.cons (searchProbe_plays_C _ _ (bL .tftSim))
        (.cons (searchProbe_plays_C _ _ (bL .tftPf))
          (.cons (searchProbe_plays_C _ _ (bL .dupoc))
            (.cons (searchProbe_plays_D _ _ (bL .ebot))
              (.cons (searchProbe_plays_C _ _ (bL .just))
                (.cons (searchProbe_plays_D _ _ (bL .obot))
                  (.cons (searchProbe_plays_D _ _ (bL .guardian)) .nil))))))))

/-- **τ(JustBot)** — Löb-gated; boundary `θ ≤ dupMass`, same as TauDupoc's. -/
theorem tauJust_phase :
    ∃ k₂, ∀ k, k₂ < k → ∀ θ (w : Tmpl → Nat) (opponent : Prog),
      (θ ≤ dupMass w → ∃ N, play N (TauBotZ k .just w θ) opponent = some .C)
      ∧ (¬ θ ≤ dupMass w → ∃ N, play N (TauBotZ k .just w θ) opponent = some .D) := by
  obtain ⟨kL, hkL⟩ := ps_probe_inst_quine
  obtain ⟨kA, hkA⟩ := linear_log2_add_le 1 8
  refine ⟨max kL kA, fun k hk θ w opponent => ?_⟩
  have hquine := hkL k (lt_of_le_of_lt (Nat.le_max_left _ _) hk)
  have hkA' : 1 * Nat.log2 k + 8 ≤ k :=
    hkA k (Nat.le_of_lt (lt_of_le_of_lt (Nat.le_max_right _ _) hk))
  have hk2 : 2 ≤ k := by omega
  have hkk : c_guard k + 3 ≤ k := by simp only [c_guard, numCost]; omega
  have hk7 : c_guard k + 7 ≤ k := by simp only [c_guard, numCost]; omega
  have h := tauPlayer_phase_bits θ (justBits hk2 hkk hk7 hquine w) opponent
  simp only [massOf, massOf_ifC, massOf_ifD, TauBotZ] at h ⊢
  simpa [dupMass] using h

end PD.Tau
