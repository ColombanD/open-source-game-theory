import PrisonersDilemma.Tau.Theorems.Columns

/-!
# τ(DupocBot)'s phase — Löb-GATED (`∃ k₂, ∀ k > k₂, …`): its diagonal bit is
the quine. Boundary `θ ≤ coopMass`, honestly EXCLUDING `w .ebot` (the floor).
-/

open PD PD.BaseTheorems

namespace PD.Tau

theorem dupocBits {k : Nat} (hk : 2 ≤ k) (hkk : c_guard k + 3 ≤ k)
    (hk7 : c_guard k + 7 ≤ k)
    (hquine : proofSearch k (probe (inst (zoo6 k) .dupoc .dupoc)) = true)
    (w : Tmpl → Nat) :
    VoteBits (vecOf (zoo6 k) .dupoc w order6)
      [(w .coop, .C), (w .defect, .D), (w .tftSim, .C),
       (w .tftPf, .C), (w .dupoc, .C), (w .ebot, .D)] :=
  -- τ(Dupoc)'s entry at T probes T's δ_L column bit ("does T, seeing ME,
  -- cooperate?"): one column read, plus the quine at the diagonal. The EBot slot
  -- is THE FLOOR: `dupocColBit .ebot = false` although the instance truly
  -- cooperates (the Gödelian pair in InstCerts).
  let bL := ps_probe_inst_dupoc hk hkk hk7 hquine
  .cons (searchProbe_plays_C _ _ (bL .coop))
    (.cons (searchProbe_plays_D _ _ (bL .defect))
      (.cons (searchProbe_plays_C _ _ (bL .tftSim))
        (.cons (searchProbe_plays_C _ _ (bL .tftPf))
          (.cons (inst_quine_plays hquine)
            (.cons (searchProbe_plays_D _ _ (bL .ebot)) .nil)))))

/-- **τ(DupocBot) α-phase theorem** — Löb-gated; the mass excludes `w .ebot`. -/
theorem tauDupoc_phase :
    ∃ k₂, ∀ k, k₂ < k → ∀ θ (w : Tmpl → Nat) (opponent : Prog),
      (θ ≤ w .coop + (w .tftSim + (w .tftPf + w .dupoc)) →
        ∃ N, play N (TauBotZ k .dupoc w θ) opponent = some .C)
      ∧ (¬ θ ≤ w .coop + (w .tftSim + (w .tftPf + w .dupoc)) →
        ∃ N, play N (TauBotZ k .dupoc w θ) opponent = some .D) := by
  obtain ⟨kL, hkL⟩ := ps_probe_inst_quine
  obtain ⟨kA, hkA⟩ := linear_log2_add_le 1 8
  refine ⟨max kL kA, fun k hk θ w opponent => ?_⟩
  have hquine := hkL k (lt_of_le_of_lt (Nat.le_max_left _ _) hk)
  have hkA' : 1 * Nat.log2 k + 8 ≤ k :=
    hkA k (Nat.le_of_lt (lt_of_le_of_lt (Nat.le_max_right _ _) hk))
  have hk2 : 2 ≤ k := by omega
  have hkk : c_guard k + 3 ≤ k := by simp only [c_guard, numCost]; omega
  have hk7 : c_guard k + 7 ≤ k := by simp only [c_guard, numCost]; omega
  have h := tauPlayer_phase_bits θ (dupocBits hk2 hkk hk7 hquine w) opponent
  simp only [massOf, massOf_ifC, massOf_ifD, TauBotZ] at h ⊢
  simpa using h

end PD.Tau
