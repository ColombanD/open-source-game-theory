import PrisonersDilemma.Tau.Theorems.Columns

/-!
# τ(CupodBot)'s phase — the suspicious cooperator, Löb-gated TWICE over.

Cupod trusts by default and punishes only what it can convict. On this zoo it
convicts exactly the defector and ITSELF (`ps_probeD_inst_cupod_quine` — the
polarity-inverted Löb quine), so its boundary is `θ ≤ cupodMass` = everything but
those two weights.

Two open bits are carried as hypotheses, with their canonical values:

* the DIAGONAL bit is the Löb threshold (like Dupoc's quine — the `∃k₂` gate);
* the `.dupoc` slot is **the entangled cell**: genuinely open (the 2-cycle is not
  Löbian, and the base τ-route does not transfer — `TauCupod/Helpers`). Its
  canonical value `.C` mirrors the base red cell `outcome_DupocBot_vs_CupodBot
  = (D, C)`: Cupod trusts, Dupoc defects. `hdc` pins the OTHER order's defection
  bit false — Dupoc-seeing-Cupod's D is an else-play the floor prices out — which
  the δ_Cu column consumes.
-/

open PD PD.BaseTheorems

namespace PD.Tau

/-- τ(Cupod)'s bit ROW. The `.dupoc` slot is supplied by hypothesis — it is the
    entangled cell, open at the object level. -/
def cupodRow (bDupoc : Action) : Tmpl → Action
  | .coop       => .C
  | .defect     => .D
  | .tftSim     => .C
  | .tftPf      => .C
  | .dupoc      => bDupoc
  | .ebot       => .C
  | .just       => .C
  | .obot       => .C
  | .guardian   => .C
  | .dbot       => .C
  | .cupodTroll => .C
  | .cupod      => .D

/-- The row's witness: one punish-probe per hypothesis, fed the δ_Cu guard column;
    the diagonal is the Löb quine, the `.dupoc` slot the open entangled play. -/
theorem cupodRow_plays {k : Nat} (hk : 2 ≤ k) (hkk : c_guard k + 3 ≤ k) (h6 : 6 ≤ k)
    (h10 : 10 ≤ k)
    (hquine : proofSearch k (probeD (inst (tauZoo k) .cupod .cupod)) = true)
    (hdc : proofSearch k (probeD (inst (tauZoo k) .dupoc .cupod)) = cupodColBit .dupoc)
    {bDupoc : Action}
    (hcdP : ∃ N, eval N (.bot (inst (tauZoo k) .cupod .dupoc))
      (.bot (inst (tauZoo k) .cupod .dupoc)) (inst (tauZoo k) .cupod .dupoc)
      = some bDupoc) :
    ∀ T, ∃ N, eval N (.bot (inst (tauZoo k) .cupod T)) (.bot (inst (tauZoo k) .cupod T))
              (inst (tauZoo k) .cupod T) = some (cupodRow bDupoc T) :=
  let bCu := ps_probeD_inst_cupod hk hkk h6 h10 hquine hdc
  fun T => match T with
  | .coop       => searchProbeD_plays_C _ _ (bCu .coop)
  | .defect     => searchProbeD_plays_D _ _ (bCu .defect)
  | .tftSim     => searchProbeD_plays_C _ _ (bCu .tftSim)
  | .tftPf      => searchProbeD_plays_C _ _ (bCu .tftPf)
  | .dupoc      => hcdP
  | .ebot       => searchProbeD_plays_C _ _ (bCu .ebot)
  | .just       => searchProbeD_plays_C _ _ (bCu .just)
  | .obot       => searchProbeD_plays_C _ _ (bCu .obot)
  | .guardian   => searchProbeD_plays_C _ _ (bCu .guardian)
  | .dbot       => searchProbeD_plays_C _ _ (bCu .dbot)
  | .cupodTroll => searchProbeD_plays_C _ _ (bCu .cupodTroll)
  | .cupod      => inst_cupod_quine_plays_D hquine

/-- The scanner-facing bit row (read by `app`'s `def4_theorems.py` — keep the
    literal list): `vecOf_bits`' mapped row, by defeq on the concrete zoo. The
    `.dupoc` literal is the CANONICAL value of the open cell, conditional on
    `hcdP`. -/
theorem cupodBits {k : Nat} (hk : 2 ≤ k) (hkk : c_guard k + 3 ≤ k) (h6 : 6 ≤ k)
    (h10 : 10 ≤ k)
    (hquine : proofSearch k (probeD (inst (tauZoo k) .cupod .cupod)) = true)
    (hdc : proofSearch k (probeD (inst (tauZoo k) .dupoc .cupod)) = cupodColBit .dupoc)
    (hcdP : ∃ N, eval N (.bot (inst (tauZoo k) .cupod .dupoc))
      (.bot (inst (tauZoo k) .cupod .dupoc)) (inst (tauZoo k) .cupod .dupoc)
      = some Action.C)
    (w : Tmpl → Nat) :
    VoteBits (vecOf (tauZoo k) .cupod w tauOrder)
      [(w .coop, .C), (w .defect, .D), (w .tftSim, .C), (w .tftPf, .C),
       (w .dupoc, .C), (w .ebot, .C), (w .just, .C), (w .obot, .C),
       (w .guardian, .C), (w .dbot, .C), (w .cupodTroll, .C), (w .cupod, .D)] :=
  vecOf_bits (tauZoo k) .cupod w (cupodRow .C) tauOrder
    fun T _ => cupodRow_plays hk hkk h6 h10 hquine hdc hcdP T

/-- **τ(CupodBot)** — Löb-gated (its diagonal is the punish-polarity quine);
    boundary `θ ≤ cupodMass`, conditional on the entangled slot's canonical
    resolution. -/
theorem tauCupod_phase :
    ∃ k₂, ∀ k, k₂ < k →
      ∀ (hdc : proofSearch k (probeD (inst (tauZoo k) .dupoc .cupod))
          = cupodColBit .dupoc)
        (hcdP : ∃ N, eval N (.bot (inst (tauZoo k) .cupod .dupoc))
          (.bot (inst (tauZoo k) .cupod .dupoc)) (inst (tauZoo k) .cupod .dupoc)
          = some Action.C),
      ∀ θ (w : Tmpl → Nat) (opponent : Prog),
      (θ ≤ cupodMass w → ∃ N, play N (TauBotZ k .cupod w θ) opponent = some .C)
      ∧ (¬ θ ≤ cupodMass w → ∃ N, play N (TauBotZ k .cupod w θ) opponent = some .D) := by
  obtain ⟨kL, hkL⟩ := ps_probeD_inst_cupod_quine
  obtain ⟨kA, hkA⟩ := linear_log2_add_le 1 12
  refine ⟨max kL kA, fun k hk hdc hcdP θ w opponent => ?_⟩
  have hquine := hkL k (lt_of_le_of_lt (Nat.le_max_left _ _) hk)
  have hkA' : 1 * Nat.log2 k + 12 ≤ k :=
    hkA k (Nat.le_of_lt (lt_of_le_of_lt (Nat.le_max_right _ _) hk))
  have hk2 : 2 ≤ k := by omega
  have hkk : c_guard k + 3 ≤ k := by simp only [c_guard, numCost]; omega
  have h6 : 6 ≤ k := by omega
  have h10 : 10 ≤ k := by omega
  have h := phase_of_bits (tauZoo k) .cupod w (cupodRow .C) tauOrder θ opponent
    (fun T _ => cupodRow_plays hk2 hkk h6 h10 hquine hdc hcdP T)
  simp only [bitMass, tauOrder, List.map, cupodRow, massOf, massOf_ifC, massOf_ifD,
    TauBotZ] at h ⊢
  simpa [cupodMass] using h

end PD.Tau
