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

/-- τ(TFTSim)'s bit ROW: the behavioral δ_C column — copies each hypothesis's TRUE
    play against the cooperator (Guardian's floor-priced C included). -/
def tftSimRow : Tmpl → Action
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

/-- The row's witness: every entry is a run-stage copy of the δ_C behavioral
    column. -/
theorem tftSimRow_plays {k : Nat} (hk : 2 ≤ k) (hkk : c_guard k + 3 ≤ k) (h6 : 6 ≤ k)
    (h10 : 10 ≤ k) (hL : 100 * Nat.log2 k + 1000 ≤ k) (hcg : c_guard k + 20 ≤ k) :
    ∀ T, ∃ N, eval N (.bot (inst (tauZoo k) .tftSim T)) (.bot (inst (tauZoo k) .tftSim T))
              (inst (tauZoo k) .tftSim T) = some (tftSimRow T) :=
  let pC := inst_coop_plays hk hkk h6 h10 hL
  fun T => match T with
  | .coop     => simCopy_plays _ _ (pC .coop)
  | .defect   => simCopy_plays _ _ (pC .defect)
  | .tftSim   => simCopy_plays _ _ (pC .tftSim)
  | .tftPf    => simCopy_plays _ _ (pC .tftPf)
  | .dupoc    => simCopy_plays _ _ (pC .dupoc)
  | .ebot     => simCopy_plays _ _ (pC .ebot)
  | .just     => simCopy_plays _ _ (pC .just)
  | .obot     => simCopy_plays _ _ (pC .obot)
  | .guardian => simCopy_plays _ _ (pC .guardian)
  | .dbot     => simCopy_plays _ _ (pC .dbot)
  | .cupod      => simCopy_plays _ _ (pC .cupod)
  | .cupodTroll => simCopy_plays _ _ (pC .cupodTroll)
  | .cimcic     => simCopy_plays _ _ (pC .cimcic)

/-- The scanner-facing bit row (read by `app`'s `def4_theorems.py` — keep the
    literal list): `vecOf_bits`' mapped row, by defeq on the concrete zoo. -/
theorem tftSimBits {k : Nat} (hk : 2 ≤ k) (hkk : c_guard k + 3 ≤ k) (h6 : 6 ≤ k)
    (h10 : 10 ≤ k) (hL : 100 * Nat.log2 k + 1000 ≤ k) (hcg : c_guard k + 20 ≤ k) (w : Tmpl → Nat) :
    VoteBits (vecOf (tauZoo k) .tftSim w tauOrder)
      [(w .coop, .C), (w .defect, .D), (w .tftSim, .C), (w .tftPf, .C),
       (w .dupoc, .C), (w .ebot, .D), (w .just, .C), (w .obot, .C),
       (w .guardian, .C), (w .dbot, .D), (w .cupodTroll, .C), (w .cupod, .C), (w .cimcic, .C)] :=
  vecOf_bits (tauZoo k) .tftSim w tftSimRow tauOrder
    fun T _ => tftSimRow_plays hk hkk h6 h10 hL hcg T

/-- **τ(TitForTatBot), behavioral** — boundary `θ ≤ simMass` (incl. Guardian). -/
theorem tauTFTSim_phase {k : Nat} (hk : 2 ≤ k) (hkk : c_guard k + 3 ≤ k) (h6 : 6 ≤ k)
    (h10 : 10 ≤ k) (hL : 100 * Nat.log2 k + 1000 ≤ k) (hcg : c_guard k + 20 ≤ k) (θ : Nat) (w : Tmpl → Nat) (opponent : Prog) :
    (θ ≤ simMass w → ∃ N, play N (TauBotZ k .tftSim w θ) opponent = some .C)
    ∧ (¬ θ ≤ simMass w → ∃ N, play N (TauBotZ k .tftSim w θ) opponent = some .D) := by
  have h := phase_of_bits (tauZoo k) .tftSim w tftSimRow tauOrder θ opponent
    (fun T _ => tftSimRow_plays hk hkk h6 h10 hL hcg T)
  simp only [bitMass, tauOrder, List.map, tftSimRow, massOf, massOf_ifC, massOf_ifD,
    TauBotZ] at h ⊢
  simpa [simMass] using h

end PD.Tau
