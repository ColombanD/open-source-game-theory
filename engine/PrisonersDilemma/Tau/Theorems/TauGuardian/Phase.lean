import PrisonersDilemma.Tau.Theorems.Columns

/-!
# τ(GuardianBot)'s phase — boundary `θ ≤ guardMass = simMass`.

The norm enforcer trusts everyone it cannot convict of bullying the cooperator: it
punishes exactly Defect and EBot (the two provable bullies) and cooperates with the
rest — including itself and the behavioral bots. Its mass coincides with
TauTFTSim's, though for inverted reasons: TFTSim SEES everyone's true cooperation;
Guardian merely FAILS TO CONVICT the same set.
-/

open PD PD.BaseTheorems

namespace PD.Tau

theorem guardianBits {k : Nat} (hk : 2 ≤ k) (hkk : c_guard k + 3 ≤ k) (h6 : 6 ≤ k)
    (h10 : 10 ≤ k) (w : Tmpl → Nat) :
    VoteBits (vecOf (tauZoo k) .guardian w tauOrder)
      [(w .coop, .C), (w .defect, .D), (w .tftSim, .C), (w .tftPf, .C),
       (w .dupoc, .C), (w .ebot, .D), (w .just, .C), (w .obot, .C),
       (w .guardian, .C)] :=
  let gB := ps_probeD_inst_coop hk hkk h6 h10
  .cons (searchProbeD_plays_C _ _ (gB .coop))
    (.cons (searchProbeD_plays_D _ _ (gB .defect))
      (.cons (searchProbeD_plays_C _ _ (gB .tftSim))
        (.cons (searchProbeD_plays_C _ _ (gB .tftPf))
          (.cons (searchProbeD_plays_C _ _ (gB .dupoc))
            (.cons (searchProbeD_plays_D _ _ (gB .ebot))
              (.cons (searchProbeD_plays_C _ _ (gB .just))
                (.cons (searchProbeD_plays_C _ _ (gB .obot))
                  (.cons (searchProbeD_plays_C _ _ (gB .guardian)) .nil))))))))

/-- **τ(GuardianBot)** — boundary `θ ≤ guardMass`. -/
theorem tauGuardian_phase {k : Nat} (hk : 2 ≤ k) (hkk : c_guard k + 3 ≤ k) (h6 : 6 ≤ k)
    (h10 : 10 ≤ k) (θ : Nat) (w : Tmpl → Nat) (opponent : Prog) :
    (θ ≤ guardMass w → ∃ N, play N (TauBotZ k .guardian w θ) opponent = some .C)
    ∧ (¬ θ ≤ guardMass w → ∃ N, play N (TauBotZ k .guardian w θ) opponent = some .D) := by
  have h := tauPlayer_phase_bits θ (guardianBits hk hkk h6 h10 w) opponent
  simp only [massOf, massOf_ifC, massOf_ifD, TauBotZ] at h ⊢
  simpa [guardMass, simMass] using h

end PD.Tau
