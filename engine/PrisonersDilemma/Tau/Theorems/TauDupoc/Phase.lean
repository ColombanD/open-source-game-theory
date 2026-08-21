import PrisonersDilemma.Tau.Theorems.Columns

/-!
# τ(DupocBot)'s phase — Löb-GATED: its diagonal bit is the quine.

Boundary `θ ≤ dupMass` — excluding `w .ebot` and `w .guardian` (both floors) and
`w .obot` (a true defection: OBot's second watch catches Dupoc defecting against
the defector).
-/

open PD PD.BaseTheorems

namespace PD.Tau

/-- τ(DupocBot)'s bit ROW: the prover δ_L column, with the QUINE on the
    diagonal. -/
def dupocRow : Tmpl → Action
  | .coop     => .C
  | .defect   => .D
  | .tftSim   => .C
  | .tftPf    => .C
  | .dupoc    => .C
  | .ebot     => .D
  | .just     => .C
  | .obot     => .D
  | .guardian => .D
  | .dbot     => .D
  | .cupod      => .D
  | .cupodTroll => .D

/-- The row's witness: prove-stages on the δ_L column; the diagonal is the Löb
    quine, supplied as a hypothesis. -/
theorem dupocRow_plays {k : Nat} (hk : 2 ≤ k) (hkk : c_guard k + 3 ≤ k)
    (hk7 : c_guard k + 7 ≤ k)
    (hquine : proofSearch k (probe (inst (tauZoo k) .dupoc .dupoc)) = true)
    (hcd : proofSearch k (probe (inst (tauZoo k) .cupod .dupoc)) = dupocColBit .cupod)
    (hcdPlay : ∃ N, eval N (.bot (inst (tauZoo k) .dupoc .cupod))
      (.bot (inst (tauZoo k) .dupoc .cupod)) (inst (tauZoo k) .dupoc .cupod)
      = some (dupocRow .cupod)) :
    ∀ T, ∃ N, eval N (.bot (inst (tauZoo k) .dupoc T)) (.bot (inst (tauZoo k) .dupoc T))
              (inst (tauZoo k) .dupoc T) = some (dupocRow T) :=
  let bL := ps_probe_inst_dupoc hk hkk hk7 hquine hcd
  fun T => match T with
  | .coop     => searchProbe_plays_C _ _ (bL .coop)
  | .defect   => searchProbe_plays_D _ _ (bL .defect)
  | .tftSim   => searchProbe_plays_C _ _ (bL .tftSim)
  | .tftPf    => searchProbe_plays_C _ _ (bL .tftPf)
  | .dupoc    => inst_quine_plays hquine
  | .ebot     => searchProbe_plays_D _ _ (bL .ebot)
  | .just     => searchProbe_plays_C _ _ (bL .just)
  | .obot     => searchProbe_plays_D _ _ (bL .obot)
  | .guardian => searchProbe_plays_D _ _ (bL .guardian)
  | .dbot     => searchProbe_plays_D _ _ (bL .dbot)
  | .cupod      => hcdPlay   -- the entangled cell: open (see TauCupod/Helpers)
  | .cupodTroll => searchProbe_plays_D _ _ (bL .cupodTroll)

/-- The scanner-facing bit row (read by `app`'s `def4_theorems.py` — keep the
    literal list): `vecOf_bits`' mapped row, by defeq on the concrete zoo. -/
theorem dupocBits {k : Nat} (hk : 2 ≤ k) (hkk : c_guard k + 3 ≤ k)
    (hk7 : c_guard k + 7 ≤ k)
    (hquine : proofSearch k (probe (inst (tauZoo k) .dupoc .dupoc)) = true)
    (hcd : proofSearch k (probe (inst (tauZoo k) .cupod .dupoc)) = dupocColBit .cupod)
    (hcdPlay : ∃ N, eval N (.bot (inst (tauZoo k) .dupoc .cupod))
      (.bot (inst (tauZoo k) .dupoc .cupod)) (inst (tauZoo k) .dupoc .cupod)
      = some (dupocRow .cupod))
    (w : Tmpl → Nat) :
    VoteBits (vecOf (tauZoo k) .dupoc w tauOrder)
      [(w .coop, .C), (w .defect, .D), (w .tftSim, .C), (w .tftPf, .C),
       (w .dupoc, .C), (w .ebot, .D), (w .just, .C), (w .obot, .D),
       (w .guardian, .D), (w .dbot, .D), (w .cupodTroll, .D), (w .cupod, .D)] :=
  vecOf_bits (tauZoo k) .dupoc w dupocRow tauOrder
    fun T _ => dupocRow_plays hk hkk hk7 hquine hcd hcdPlay T

/-- **τ(DupocBot)** — Löb-gated; boundary `θ ≤ dupMass`. -/
theorem tauDupoc_phase :
    ∃ k₂, ∀ k, k₂ < k →
      -- the entangled `.cupod` bit is genuinely OPEN (the 2-cycle is not Löbian —
      -- see `TauCupod/Helpers`), so it is a hypothesis, exactly as the quine bit was
      ∀ (hcd : proofSearch k (probe (inst (tauZoo k) .cupod .dupoc)) = dupocColBit .cupod)
        (hcdPlay : ∃ N, eval N (.bot (inst (tauZoo k) .dupoc .cupod))
          (.bot (inst (tauZoo k) .dupoc .cupod)) (inst (tauZoo k) .dupoc .cupod)
          = some (dupocRow .cupod)),
      ∀ θ (w : Tmpl → Nat) (opponent : Prog),
      (θ ≤ dupMass w → ∃ N, play N (TauBotZ k .dupoc w θ) opponent = some .C)
      ∧ (¬ θ ≤ dupMass w → ∃ N, play N (TauBotZ k .dupoc w θ) opponent = some .D) := by
  obtain ⟨kL, hkL⟩ := ps_probe_inst_quine
  obtain ⟨kA, hkA⟩ := linear_log2_add_le 1 8
  refine ⟨max kL kA, fun k hk hcd hcdPlay θ w opponent => ?_⟩
  have hquine := hkL k (lt_of_le_of_lt (Nat.le_max_left _ _) hk)
  have hkA' : 1 * Nat.log2 k + 8 ≤ k :=
    hkA k (Nat.le_of_lt (lt_of_le_of_lt (Nat.le_max_right _ _) hk))
  have hk2 : 2 ≤ k := by omega
  have hkk : c_guard k + 3 ≤ k := by simp only [c_guard, numCost]; omega
  have hk7 : c_guard k + 7 ≤ k := by simp only [c_guard, numCost]; omega
  have h := phase_of_bits (tauZoo k) .dupoc w dupocRow tauOrder θ opponent
    (fun T _ => dupocRow_plays hk2 hkk hk7 hquine hcd hcdPlay T)
  simp only [bitMass, tauOrder, List.map, dupocRow, massOf, massOf_ifC, massOf_ifD,
    TauBotZ] at h ⊢
  simpa [dupMass] using h

end PD.Tau
