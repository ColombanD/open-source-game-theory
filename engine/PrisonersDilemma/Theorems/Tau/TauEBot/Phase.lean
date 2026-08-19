import PrisonersDilemma.Theorems.Tau.Columns

/-!
# τ(EBot)'s phase — the ONE-SIDED boundary `θ ≤ eMass` (no window): it excludes
`w .coop`, the weight EBot exploits. The corrected bot of the 2026-08-13
retraction; the crowd-exploiter's window has no counterpart here.
-/

open PD PD.BaseTheorems

namespace PD.Tau

theorem eBits {k : Nat} (hk : 2 ≤ k) (hkk : c_guard k + 3 ≤ k) (h6 : 6 ≤ k)
    (w : Tmpl → Nat) :
    VoteBits (vecOf (zoo6 k) .ebot w order6)
      [(w .coop, .D), (w .defect, .D), (w .tftSim, .C),
       (w .tftPf, .C), (w .dupoc, .C), (w .ebot, .D)] :=
  -- τ(EBot)'s entry at hypothesis T is the cascade over T's δ_D and δ_C column
  -- bits, so the whole table is TWO column reads.
  let bD := ps_probe_inst_defect (k := k) hk
  let bC := ps_probe_inst_coop hk hkk h6
  .cons (cascade_plays_D_of_exploit _ _ (bD .coop))
    (.cons (cascade_plays_D_of_both_false _ _ (bD .defect) (bC .defect))
      (.cons (cascade_plays_C _ _ (bD .tftSim) (bC .tftSim))
        (.cons (cascade_plays_C _ _ (bD .tftPf) (bC .tftPf))
          (.cons (cascade_plays_C _ _ (bD .dupoc) (bC .dupoc))
            (.cons (cascade_plays_D_of_both_false _ _ (bD .ebot) (bC .ebot)) .nil)))))

/-- **τ(EBot) α-phase theorem — the ONE-SIDED boundary** `θ ≤ wTs + wTp + wL`. -/
theorem tauEBot_phase {k : Nat} (hk : 2 ≤ k) (hkk : c_guard k + 3 ≤ k) (h6 : 6 ≤ k)
    (θ : Nat) (w : Tmpl → Nat) (opponent : Prog) :
    (θ ≤ w .tftSim + (w .tftPf + w .dupoc) →
      ∃ N, play N (TauBotZ k .ebot w θ) opponent = some .C)
    ∧ (¬ θ ≤ w .tftSim + (w .tftPf + w .dupoc) →
      ∃ N, play N (TauBotZ k .ebot w θ) opponent = some .D) := by
  have h := tauPlayer_phase_bits θ (eBits hk hkk h6 w) opponent
  simp only [massOf, massOf_ifC, massOf_ifD, TauBotZ] at h ⊢
  simpa using h

end PD.Tau
