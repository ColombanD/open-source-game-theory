import PrisonersDilemma.Tau.Theorems.Columns

/-!
# τ(EBot)'s phase — the ONE-SIDED boundary `θ ≤ eMass`.

Excludes `w .coop` (the weight it exploits) and now also `w .guardian`: EBot's
reciprocity probe cannot cite Guardian's floor-priced cooperation, so the exploiter
DEFECTS on the norm enforcer — mutual illegibility between the two prover
specialists.
-/

open PD PD.BaseTheorems

namespace PD.Tau

theorem eBits {k : Nat} (hk : 2 ≤ k) (hkk : c_guard k + 3 ≤ k) (h6 : 6 ≤ k)
    (h10 : 10 ≤ k) (w : Tmpl → Nat) :
    VoteBits (vecOf (tauZoo k) .ebot w tauOrder)
      [(w .coop, .D), (w .defect, .D), (w .tftSim, .C), (w .tftPf, .C),
       (w .dupoc, .C), (w .ebot, .D), (w .just, .C), (w .obot, .C),
       (w .guardian, .D)] :=
  let bD := ps_probe_inst_defect (k := k) hk
  let bC := ps_probe_inst_coop hk hkk h6 h10
  .cons (cascade_plays_D_of_exploit _ _ (bD .coop))
    (.cons (cascade_plays_D_of_both_false _ _ (bD .defect) (bC .defect))
      (.cons (cascade_plays_C _ _ (bD .tftSim) (bC .tftSim))
        (.cons (cascade_plays_C _ _ (bD .tftPf) (bC .tftPf))
          (.cons (cascade_plays_C _ _ (bD .dupoc) (bC .dupoc))
            (.cons (cascade_plays_D_of_both_false _ _ (bD .ebot) (bC .ebot))
              (.cons (cascade_plays_C _ _ (bD .just) (bC .just))
                (.cons (cascade_plays_C _ _ (bD .obot) (bC .obot))
                  (.cons (cascade_plays_D_of_both_false _ _ (bD .guardian) (bC .guardian))
                    .nil))))))))

/-- **τ(EBot)** — one-sided boundary `θ ≤ eMass`, no window. -/
theorem tauEBot_phase {k : Nat} (hk : 2 ≤ k) (hkk : c_guard k + 3 ≤ k) (h6 : 6 ≤ k)
    (h10 : 10 ≤ k) (θ : Nat) (w : Tmpl → Nat) (opponent : Prog) :
    (θ ≤ eMass w → ∃ N, play N (TauBotZ k .ebot w θ) opponent = some .C)
    ∧ (¬ θ ≤ eMass w → ∃ N, play N (TauBotZ k .ebot w θ) opponent = some .D) := by
  have h := tauPlayer_phase_bits θ (eBits hk hkk h6 h10 w) opponent
  simp only [massOf, massOf_ifC, massOf_ifD, TauBotZ] at h ⊢
  simpa [eMass] using h

end PD.Tau
