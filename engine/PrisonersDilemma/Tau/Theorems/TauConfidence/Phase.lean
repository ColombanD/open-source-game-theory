import PrisonersDilemma.Tau.Theorems.TauDupoc.Phase
import PrisonersDilemma.Tau.RowSpec
import PrisonersDilemma.Outcome.Attr

/-!
# ConfidenceBot's row and phase (native, 2026-08-27)

**The row is Dupoc's.** ConfidenceBot's per-hypothesis TEST is Dupoc's, so its
instances are Dupoc's by `rfl` (`Zoo.lean`'s bridges) at every slot but three: the
`confidence × dupoc` system (mutual Löb, C — `TauConfidence/Helpers`), its own
diagonal (Dupoc's quine term, C) and the `.just` slot (Just-facing-Confidence probes
that system; C past the same Löb threshold). Same VALUES as `dupocRow` everywhere —
`confidenceRow_eq_dupocRow` — which is the kernel form of "in the hypothesis role
ConfidenceBot is Dupoc".

**The phase is NOT Dupoc's.** `ConfidenceBotZ` is the MAX chain over that row:
it cooperates iff some single hypothesis carrying at least θ of the signal has a C
bit (`tauConfidence_phase`, readable form `tauConfidence_phase'`). And that is the
lift of no template at all: `confidence_not_linear` exhibits three signals on which
the max plays C, D, C while `θ' ≤ bitMass w r` — every lift's play, by
`phase_of_bits` — cannot, whatever the row `r` and threshold `θ'`.
-/

open PD PD.BaseTheorems

namespace PD.Tau

/-- ConfidenceBot's bit ROW — Dupoc's values, with the two new Löb cells. -/
def confidenceRow : Tmpl → Action
  | .coop       => .C
  | .defect     => .D
  | .tftSim     => .C
  | .tftPf      => .C
  | .dupoc      => .C
  | .ebot       => .D
  | .just       => .C
  | .obot       => .D
  | .guardian   => .D
  | .dbot       => .D
  | .cupod      => .D
  | .cupodTroll => .D
  | .cimcic     => .C
  | .dimcid     => .D
  | .prudent    => .D
  | .confidence => .C
  | .mirror     => .C

theorem confidenceRow_eq_dupocRow : confidenceRow = dupocRow := by
  funext T; cases T <;> rfl

/-- The row's witness: Dupoc's witness through the bridges, plus the three cells
    that reach the `confidence × dupoc` system. -/
theorem confidenceRow_plays {k : Nat} (hk : 2 ≤ k) (hkk : c_guard k + 3 ≤ k)
    (hk7 : c_guard k + 7 ≤ k)
    (hquine : proofSearch k (probe (inst (tauZoo k) .dupoc .dupoc)) = true)
    (hcim : proofSearch k (probe (inst (tauZoo k) .cimcic .dupoc)) = dupocColBit .cimcic)
    (hmir : proofSearch k (probe (inst (tauZoo k) .mirror .dupoc)) = dupocColBit .mirror)
    (hconf : proofSearch k (probe (inst (tauZoo k) .confidence .dupoc))
      = dupocColBit .confidence)
    (hcfP : ∃ N, eval N (.bot (inst (tauZoo k) .confidence .dupoc))
      (.bot (inst (tauZoo k) .confidence .dupoc)) (inst (tauZoo k) .confidence .dupoc)
      = some Action.C)
    (hmirP : ∃ N, eval N (.bot (inst (tauZoo k) .dupoc .mirror))
      (.bot (inst (tauZoo k) .dupoc .mirror)) (inst (tauZoo k) .dupoc .mirror)
      = some (dupocRow .mirror))
    (hdmP : ∃ N, eval N (.bot (inst (tauZoo k) .dupoc .cimcic))
      (.bot (inst (tauZoo k) .dupoc .cimcic)) (inst (tauZoo k) .dupoc .cimcic)
      = some (dupocRow .cimcic)) :
    ∀ T, ∃ N, eval N (.bot (inst (tauZoo k) .confidence T))
              (.bot (inst (tauZoo k) .confidence T))
              (inst (tauZoo k) .confidence T) = some (confidenceRow T) := by
  have hcfP' : ∃ N, eval N (.bot (inst (tauZoo k) .dupoc .confidence))
      (.bot (inst (tauZoo k) .dupoc .confidence)) (inst (tauZoo k) .dupoc .confidence)
      = some (dupocRow .confidence) := by
    rw [inst_dupoc_confidence_eq]; rw [inst_confidence_dupoc_eq] at hcfP; exact hcfP
  have hD := dupocRow_plays hk hkk hk7 hquine hcim hmir hconf hcfP' hmirP hdmP
  intro T
  cases T with
  | dupoc => exact hcfP
  | confidence => rw [inst_confidence_quine]; exact inst_quine_plays hquine
  | just => exact searchProbe_plays_C _ _ (ps_probe_just_confidence hkk hconf)
  | coop => rw [inst_confidence_eq_dupoc k .coop (by decide) (by decide) (by decide)]; exact hD .coop
  | defect => rw [inst_confidence_eq_dupoc k .defect (by decide) (by decide) (by decide)]; exact hD .defect
  | tftSim => rw [inst_confidence_eq_dupoc k .tftSim (by decide) (by decide) (by decide)]; exact hD .tftSim
  | tftPf => rw [inst_confidence_eq_dupoc k .tftPf (by decide) (by decide) (by decide)]; exact hD .tftPf
  | ebot => rw [inst_confidence_eq_dupoc k .ebot (by decide) (by decide) (by decide)]; exact hD .ebot
  | obot => rw [inst_confidence_eq_dupoc k .obot (by decide) (by decide) (by decide)]; exact hD .obot
  | guardian => rw [inst_confidence_eq_dupoc k .guardian (by decide) (by decide) (by decide)]; exact hD .guardian
  | dbot => rw [inst_confidence_eq_dupoc k .dbot (by decide) (by decide) (by decide)]; exact hD .dbot
  | cupod => rw [inst_confidence_eq_dupoc k .cupod (by decide) (by decide) (by decide)]; exact hD .cupod
  | cupodTroll => rw [inst_confidence_eq_dupoc k .cupodTroll (by decide) (by decide) (by decide)]; exact hD .cupodTroll
  | cimcic => rw [inst_confidence_eq_dupoc k .cimcic (by decide) (by decide) (by decide)]; exact hD .cimcic
  | dimcid => rw [inst_confidence_eq_dupoc k .dimcid (by decide) (by decide) (by decide)]; exact hD .dimcid
  | prudent => rw [inst_confidence_eq_dupoc k .prudent (by decide) (by decide) (by decide)]; exact hD .prudent
  | mirror => rw [inst_confidence_eq_dupoc k .mirror (by decide) (by decide) (by decide)]; exact hD .mirror

/-- **ConfidenceBot's row** — the matrix-facing statement (`@[tau_row]`: validated by
    `Tau/Lint.lean`, exported to the app): unconditional at large `k`. -/
@[tau_row]
theorem confidenceRowSpec : RowSpec .confidence tauOrder confidenceRow := by
  obtain ⟨kL, hkL⟩ := ps_probe_inst_quine
  obtain ⟨kA, hkA⟩ := linear_log2_add_le 1 8
  obtain ⟨kM, hkM⟩ := ps_probe_inst_cimcic_dupoc
  obtain ⟨kP, hkP⟩ := dupoc_cimcic_plays_C
  obtain ⟨kX, hkX⟩ := ps_probe_mirror_dupoc
  obtain ⟨kY, hkY⟩ := dupoc_mirror_plays_C
  obtain ⟨kC, hkC⟩ := ps_probe_inst_confidence_dupoc
  obtain ⟨kD, hkD⟩ := confidence_dupoc_plays_C
  refine ⟨kL + kA + kM + kP + kX + kY + kC + kD, fun k hk T _ => ?_⟩
  have hquine := hkL k (by omega)
  have hkA' : 1 * Nat.log2 k + 8 ≤ k := hkA k (by omega)
  have hcim := hkM k (by omega)
  have hdmP := hkP k (by omega)
  have hmir := hkX k (by omega)
  have hmirP := hkY k (by omega)
  have hconf := hkC k (by omega)
  have hcfP := hkD k (by omega)
  have hk2 : 2 ≤ k := by omega
  have hkk : c_guard k + 3 ≤ k := by simp only [c_guard, numCost]; omega
  have hk7 : c_guard k + 7 ≤ k := by simp only [c_guard, numCost]; omega
  exact confidenceRow_plays hk2 hkk hk7 hquine hcim hmir hconf hcfP hmirP hdmP T

/-- **ConfidenceBot's phase** — the MAX aggregator over its row: C iff some single
    hypothesis carrying at least θ of the signal has a C bit. Unconditional at
    large `k`. -/
theorem tauConfidence_phase :
    ∃ k₂, ∀ k, k₂ < k →
      ∀ θ (w : Tmpl → Nat) (opponent : Prog),
      (maxHit θ (tauOrder.map fun T => (w T, confidenceRow T)) = true →
        ∃ N, play N (ConfidenceBotZ k w θ) opponent = some .C)
      ∧ (maxHit θ (tauOrder.map fun T => (w T, confidenceRow T)) = false →
        ∃ N, play N (ConfidenceBotZ k w θ) opponent = some .D) := by
  obtain ⟨k₂, hrow⟩ := confidenceRowSpec
  refine ⟨k₂, fun k hk θ w opponent => ?_⟩
  have hbits := vecOf_bits (tauZoo k) .confidence w confidenceRow tauOrder (hrow k hk)
  exact maxPlayer_phase_bits θ hbits opponent

/-- The readable form of the C-regime: `θ = 0`, or some hypothesis with a C bit
    carries at least `θ` on its own. -/
theorem tauConfidence_phase' :
    ∃ k₂, ∀ k, k₂ < k →
      ∀ θ (w : Tmpl → Nat) (opponent : Prog),
      (θ = 0 ∨ ∃ T ∈ tauOrder, θ ≤ w T ∧ confidenceRow T = .C) →
        ∃ N, play N (ConfidenceBotZ k w θ) opponent = some .C := by
  obtain ⟨k₂, h⟩ := tauConfidence_phase
  refine ⟨k₂, fun k hk θ w opponent hC => (h k hk θ w opponent).1 ?_⟩
  rw [maxHit_true_iff]
  rcases hC with h0 | ⟨T, hT, hw, hb⟩
  · exact Or.inl ⟨h0, by simp [tauOrder]⟩
  · exact Or.inr ⟨(w T, confidenceRow T), List.mem_map.2 ⟨T, hT, rfl⟩, hw, hb⟩

/-- **ConfidenceBot is the lift of NO template.** Every lift's play is `θ' ≤ bitMass w r`
    for its row `r` (`phase_of_bits`); the max is not, for ANY `r` and `θ'`: on the
    signals `2·δ_coop`, `δ_coop + δ_tftSim`, `2·δ_tftSim` (both slots C in
    `confidenceRow`) ConfidenceBot plays C, D, C at `θ = 2`, and a threshold of a
    linear mass cannot — agreeing on the first two forces `r .coop = C`, `r .tftSim = D`
    and `θ' ≤ 2`, which plays D on the third. -/
theorem confidence_not_linear :
    ¬ ∃ (θ' : Nat) (r : Tmpl → Action), ∀ w : Tmpl → Nat,
      decide (θ' ≤ bitMass w r tauOrder)
        = maxHit 2 (tauOrder.map fun T => (w T, confidenceRow T)) := by
  rintro ⟨θ', r, h⟩
  have h1 := h (fun T => if T = .coop then 2 else 0)
  have h2 := h (fun T => if T = .coop ∨ T = .tftSim then 1 else 0)
  have h3 := h (fun T => if T = .tftSim then 2 else 0)
  have e1 : maxHit 2 (tauOrder.map fun T =>
      ((fun T : Tmpl => if T = .coop then 2 else 0) T, confidenceRow T)) = true := by decide
  have e2 : maxHit 2 (tauOrder.map fun T =>
      ((fun T : Tmpl => if T = .coop ∨ T = .tftSim then 1 else 0) T, confidenceRow T)) = false := by
    decide
  have e3 : maxHit 2 (tauOrder.map fun T =>
      ((fun T : Tmpl => if T = .tftSim then 2 else 0) T, confidenceRow T)) = true := by decide
  rw [e1] at h1; rw [e2] at h2; rw [e3] at h3
  simp only [bitMass, tauOrder, List.map, massOf, decide_eq_true_eq, decide_eq_false_iff_not] at h1 h2 h3
  simp at h1 h2 h3
  cases hc : r .coop <;> cases ht : r .tftSim <;> simp [hc, ht] at h1 h2 h3 <;> omega

end PD.Tau
