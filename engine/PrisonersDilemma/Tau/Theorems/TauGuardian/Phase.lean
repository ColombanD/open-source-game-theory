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

/-- τ(GuardianBot)'s bit ROW: trust-by-default — D exactly at the two provable
    bullies. Identical values to `tftSimRow`, for inverted reasons. -/
def guardianRow : Tmpl → Action
  | .coop     => .C
  | .defect   => .D
  | .tftSim   => .C
  | .tftPf    => .C
  | .dupoc    => .C
  | .ebot     => .D
  | .just     => .C
  | .obot     => .C
  | .guardian => .C
  | .dbot     => .D
  | .cupod      => .C
  | .cupodTroll => .C
  | .cimcic     => .C
  | .dimcid     => .C
  | .prudent    => .C
  | .mirror     => .C

/-- The row's witness: every entry is the punish-probe (`test = .D` prove-stage)
    fed the guard column's bits. -/
theorem guardianRow_plays {k : Nat} (hk : 2 ≤ k) (hkk : c_guard k + 3 ≤ k) (h6 : 6 ≤ k)
    (h10 : 10 ≤ k) (hL : 100 * Nat.log2 k + 1000 ≤ k) (hcg : c_guard k + 20 ≤ k) :
    ∀ T, ∃ N, eval N (.bot (inst (tauZoo k) .guardian T))
              (.bot (inst (tauZoo k) .guardian T))
              (inst (tauZoo k) .guardian T) = some (guardianRow T) :=
  let gB := ps_probeD_inst_coop hk hkk h6 h10 hL
  fun T => match T with
  | .coop     => searchProbeD_plays_C _ _ (gB .coop)
  | .defect   => searchProbeD_plays_D _ _ (gB .defect)
  | .tftSim   => searchProbeD_plays_C _ _ (gB .tftSim)
  | .tftPf    => searchProbeD_plays_C _ _ (gB .tftPf)
  | .dupoc    => searchProbeD_plays_C _ _ (gB .dupoc)
  | .ebot     => searchProbeD_plays_D _ _ (gB .ebot)
  | .just     => searchProbeD_plays_C _ _ (gB .just)
  | .obot     => searchProbeD_plays_C _ _ (gB .obot)
  | .guardian => searchProbeD_plays_C _ _ (gB .guardian)
  | .dbot     => searchProbeD_plays_D _ _ (gB .dbot)
  | .cupod      => searchProbeD_plays_C _ _ (gB .cupod)
  | .cupodTroll => searchProbeD_plays_C _ _ (gB .cupodTroll)
  | .cimcic     => searchProbeD_plays_C _ _ (gB .cimcic)
  | .dimcid     => searchProbeD_plays_C _ _ (gB .dimcid)
  | .prudent    => searchProbeD_plays_C _ _ (gB .prudent)
  | .mirror     => searchProbeD_plays_C _ _ (gB .mirror)

/-- The scanner-facing bit row (read by `app`'s `def4_theorems.py` — keep the
    literal list): `vecOf_bits`' mapped row, by defeq on the concrete zoo. -/
theorem guardianBits {k : Nat} (hk : 2 ≤ k) (hkk : c_guard k + 3 ≤ k) (h6 : 6 ≤ k)
    (h10 : 10 ≤ k) (hL : 100 * Nat.log2 k + 1000 ≤ k) (hcg : c_guard k + 20 ≤ k) (w : Tmpl → Nat) :
    VoteBits (vecOf (tauZoo k) .guardian w tauOrder)
      [(w .coop, .C), (w .defect, .D), (w .tftSim, .C), (w .tftPf, .C),
       (w .dupoc, .C), (w .ebot, .D), (w .just, .C), (w .obot, .C),
       (w .guardian, .C), (w .dbot, .D), (w .cupodTroll, .C), (w .cupod, .C), (w .cimcic, .C), (w .dimcid, .C), (w .prudent, .C), (w .mirror, .C)] :=
  vecOf_bits (tauZoo k) .guardian w guardianRow tauOrder
    fun T _ => guardianRow_plays hk hkk h6 h10 hL hcg T

/-- **τ(GuardianBot)** — boundary `θ ≤ guardMass`. -/
theorem tauGuardian_phase {k : Nat} (hk : 2 ≤ k) (hkk : c_guard k + 3 ≤ k) (h6 : 6 ≤ k)
    (h10 : 10 ≤ k) (hL : 100 * Nat.log2 k + 1000 ≤ k) (hcg : c_guard k + 20 ≤ k) (θ : Nat) (w : Tmpl → Nat) (opponent : Prog) :
    (θ ≤ guardMass w → ∃ N, play N (TauBotZ k .guardian w θ) opponent = some .C)
    ∧ (¬ θ ≤ guardMass w → ∃ N, play N (TauBotZ k .guardian w θ) opponent = some .D) := by
  have h := phase_of_bits (tauZoo k) .guardian w guardianRow tauOrder θ opponent
    (fun T _ => guardianRow_plays hk hkk h6 h10 hL hcg T)
  simp only [bitMass, tauOrder, List.map, guardianRow, massOf, massOf_ifC, massOf_ifD,
    TauBotZ] at h ⊢
  simpa [guardMass, simMass] using h

end PD.Tau
