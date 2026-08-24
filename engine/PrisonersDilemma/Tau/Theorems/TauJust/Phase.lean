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

/-- τ(JustBot)'s bit ROW: the prover δ_L column, read by NAME — identical to
    `dupocRow`. -/
def justRow : Tmpl → Action
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
  | .cimcic     => .C
  | .dimcid     => .D
  | .mirror     => .C

/-- The row's witness: prove-stages on the δ_L column — including at the `.dupoc`
    slot, where the probed object is the quine (by name, not by self). -/
theorem justRow_plays {k : Nat} (hk : 2 ≤ k) (hkk : c_guard k + 3 ≤ k)
    (hk7 : c_guard k + 7 ≤ k)
    (hquine : proofSearch k (probe (inst (tauZoo k) .dupoc .dupoc)) = true)
    (hcim : proofSearch k (probe (inst (tauZoo k) .cimcic .dupoc)) = dupocColBit .cimcic)
    -- the mirror×dupoc entangled bit, read through the same δ_L column
    (hmir : proofSearch k (probe (inst (tauZoo k) .mirror .dupoc))
      = dupocColBit .mirror) :
    ∀ T, ∃ N, eval N (.bot (inst (tauZoo k) .just T)) (.bot (inst (tauZoo k) .just T))
              (inst (tauZoo k) .just T) = some (justRow T) :=
  let bL := ps_probe_inst_dupoc hk hkk hk7 hquine hcim hmir
  fun T => match T with
  | .coop     => searchProbe_plays_C _ _ (bL .coop)
  | .defect   => searchProbe_plays_D _ _ (bL .defect)
  | .tftSim   => searchProbe_plays_C _ _ (bL .tftSim)
  | .tftPf    => searchProbe_plays_C _ _ (bL .tftPf)
  | .dupoc    => searchProbe_plays_C _ _ (bL .dupoc)
  | .ebot     => searchProbe_plays_D _ _ (bL .ebot)
  | .just     => searchProbe_plays_C _ _ (bL .just)
  | .obot     => searchProbe_plays_D _ _ (bL .obot)
  | .guardian => searchProbe_plays_D _ _ (bL .guardian)
  | .dbot     => searchProbe_plays_D _ _ (bL .dbot)
  | .cupod      => searchProbe_plays_D _ _ (bL .cupod)
  | .cupodTroll => searchProbe_plays_D _ _ (bL .cupodTroll)
  | .cimcic     => searchProbe_plays_C _ _ (bL .cimcic)
  | .dimcid     => searchProbe_plays_D _ _ (bL .dimcid)
  | .mirror     => searchProbe_plays_C _ _ (bL .mirror)

/-- The scanner-facing bit row (read by `app`'s `def4_theorems.py` — keep the
    literal list): `vecOf_bits`' mapped row, by defeq on the concrete zoo. -/
theorem justBits {k : Nat} (hk : 2 ≤ k) (hkk : c_guard k + 3 ≤ k)
    (hk7 : c_guard k + 7 ≤ k)
    (hquine : proofSearch k (probe (inst (tauZoo k) .dupoc .dupoc)) = true)
    (hcim : proofSearch k (probe (inst (tauZoo k) .cimcic .dupoc)) = dupocColBit .cimcic)
    (hmir : proofSearch k (probe (inst (tauZoo k) .mirror .dupoc))
      = dupocColBit .mirror)
    (w : Tmpl → Nat) :
    VoteBits (vecOf (tauZoo k) .just w tauOrder)
      [(w .coop, .C), (w .defect, .D), (w .tftSim, .C), (w .tftPf, .C),
       (w .dupoc, .C), (w .ebot, .D), (w .just, .C), (w .obot, .D),
       (w .guardian, .D), (w .dbot, .D), (w .cupodTroll, .D), (w .cupod, .D), (w .cimcic, .C), (w .dimcid, .D), (w .mirror, .C)] :=
  vecOf_bits (tauZoo k) .just w justRow tauOrder
    fun T _ => justRow_plays hk hkk hk7 hquine hcim hmir T

/-- **τ(JustBot)** — Löb-gated; boundary `θ ≤ dupMass`, same as TauDupoc's. -/
theorem tauJust_phase :
    ∃ k₂, ∀ k, k₂ < k →
      ∀ (hmir : proofSearch k (probe (inst (tauZoo k) .mirror .dupoc))
          = dupocColBit .mirror),
      ∀ θ (w : Tmpl → Nat) (opponent : Prog),
      (θ ≤ dupMass w → ∃ N, play N (TauBotZ k .just w θ) opponent = some .C)
      ∧ (¬ θ ≤ dupMass w → ∃ N, play N (TauBotZ k .just w θ) opponent = some .D) := by
  obtain ⟨kL, hkL⟩ := ps_probe_inst_quine
  obtain ⟨kA, hkA⟩ := linear_log2_add_le 1 8
  obtain ⟨kM, hkM⟩ := ps_probe_inst_cimcic_dupoc
  refine ⟨max (max kL kA) kM, fun k hk hmir θ w opponent => ?_⟩
  have hquine := hkL k (lt_of_le_of_lt (le_trans (Nat.le_max_left _ _) (Nat.le_max_left _ _)) hk)
  have hkA' : 1 * Nat.log2 k + 8 ≤ k :=
    hkA k (Nat.le_of_lt (lt_of_le_of_lt (le_trans (Nat.le_max_right _ _) (Nat.le_max_left _ _)) hk))
  have hcim := hkM k (lt_of_le_of_lt (Nat.le_max_right _ _) hk)
  have hk2 : 2 ≤ k := by omega
  have hkk : c_guard k + 3 ≤ k := by simp only [c_guard, numCost]; omega
  have hk7 : c_guard k + 7 ≤ k := by simp only [c_guard, numCost]; omega
  have h := phase_of_bits (tauZoo k) .just w justRow tauOrder θ opponent
    (fun T _ => justRow_plays hk2 hkk hk7 hquine hcim hmir T)
  simp only [bitMass, tauOrder, List.map, justRow, massOf, massOf_ifC, massOf_ifD,
    TauBotZ] at h ⊢
  simpa [dupMass] using h

end PD.Tau
