import PrisonersDilemma.Tau.Theorems.Columns

/-!
# τ(OBot)'s phase — the zoo's NARROWEST boundary, `θ ≤ w .coop`.

Both defection watches must stay silent, and on this zoo only the unconditional
cooperator passes both (everyone else defects against the defector). The behavioral
defection-detector cooperates with almost nobody — but what it sees, it sees truly
(floor-blind).
-/

open PD PD.BaseTheorems

namespace PD.Tau

theorem obotBits {k : Nat} (hk : 2 ≤ k) (hkk : c_guard k + 3 ≤ k) (h6 : 6 ≤ k)
    (h10 : 10 ≤ k) (w : Tmpl → Nat) :
    VoteBits (vecOf (tauZoo k) .obot w tauOrder)
      [(w .coop, .C), (w .defect, .D), (w .tftSim, .D), (w .tftPf, .D),
       (w .dupoc, .D), (w .ebot, .D), (w .just, .D), (w .obot, .D),
       (w .guardian, .D)] :=
  let pC := inst_coop_plays hk hkk h6 h10
  let pD := inst_defect_plays (k := k) hk
  .cons (simTestD_falls _ _ (pC .coop) (simTestD_falls _ _ (pD .coop) ⟨1, rfl⟩))
    (.cons (simTestD_fires _ _ (pC .defect))
      (.cons (simTestD_falls _ _ (pC .tftSim) (simTestD_fires _ _ (pD .tftSim)))
        (.cons (simTestD_falls _ _ (pC .tftPf) (simTestD_fires _ _ (pD .tftPf)))
          (.cons (simTestD_falls _ _ (pC .dupoc) (simTestD_fires _ _ (pD .dupoc)))
            (.cons (simTestD_fires _ _ (pC .ebot))
              (.cons (simTestD_falls _ _ (pC .just) (simTestD_fires _ _ (pD .just)))
                (.cons (simTestD_falls _ _ (pC .obot) (simTestD_fires _ _ (pD .obot)))
                  (.cons (simTestD_falls _ _ (pC .guardian)
                    (simTestD_fires _ _ (pD .guardian))) .nil))))))))

/-- **τ(OBot)** — boundary `θ ≤ w .coop`. -/
theorem tauOBot_phase {k : Nat} (hk : 2 ≤ k) (hkk : c_guard k + 3 ≤ k) (h6 : 6 ≤ k)
    (h10 : 10 ≤ k) (θ : Nat) (w : Tmpl → Nat) (opponent : Prog) :
    (θ ≤ w .coop → ∃ N, play N (TauBotZ k .obot w θ) opponent = some .C)
    ∧ (¬ θ ≤ w .coop → ∃ N, play N (TauBotZ k .obot w θ) opponent = some .D) := by
  have h := tauPlayer_phase_bits θ (obotBits hk hkk h6 h10 w) opponent
  simp only [massOf, massOf_ifC, massOf_ifD, TauBotZ] at h ⊢
  simpa using h

end PD.Tau
