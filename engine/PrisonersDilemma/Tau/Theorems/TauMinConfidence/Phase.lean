import PrisonersDilemma.Tau.Theorems.TauMaxConfidence.Phase

/-!
# MinConfidenceBot's row and phase (native, 2026-09-01)

**The row is Dupoc's** — the same statement as MaxConfidenceBot's, one slot over: the
test is Dupoc's, so the instances are Dupoc's by `rfl` (`Zoo.lean`'s
`inst_minconfidence_*` bridges) at every slot but four — the two system slots
(`.dupoc` and `.maxconfidence`: the third Dupoc-spec self-prober meets the other two in
the SAME symmetric system `cfdSys`, so `TauMaxConfidence/Helpers`' mutual Löb covers
both by `rfl`), its own diagonal (Dupoc's quine term), and the `.just` slot (Just's
probe reaches the system — the same term it reaches from the `.maxconfidence` slot).
`minconfidenceRow_eq_dupocRow` is the kernel form of "in the hypothesis role
MinConfidenceBot is Dupoc".

**The phase is the WORST CASE.** `MinConfidenceBotZ` is the MIN chain over that row:
it cooperates iff NO single hypothesis carrying at least θ of the signal has a D bit
(`tauMinConfidence_phase`, readable form `tauMinConfidence_phase'`). And that is the
lift of no template: `minconfidence_not_linear` exhibits three signals — two
defectors concentrated, split, concentrated on the other — on which the min plays
D, C, D while a threshold of a linear mass cannot, the middle signal being the
average of the outer two. (The dual of `maxconfidence_not_linear`, which separates the
optimist on two COOPERATORS with the pattern C, D, C.)
-/

open PD PD.BaseTheorems

namespace PD.Tau

/-- MinConfidenceBot's bit ROW — Dupoc's values; the system cells carry the same
    mutual-Löb C as MaxConfidenceBot's. -/
def minconfidenceRow : Tmpl → Action
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
  | .maxconfidence => .C
  | .minconfidence => .C
  | .mirror     => .C

theorem minconfidenceRow_eq_dupocRow : minconfidenceRow = dupocRow := by
  funext T; cases T <;> rfl

/-- The row's witness: Dupoc's witness through the bridges; the `.dupoc` and
    `.maxconfidence` slots are the ONE system `cfdSys` (so `hcfP` covers both by
    `rfl`), the diagonal is Dupoc's quine, and the `.just` slot probes the system
    exactly as it does from the `.maxconfidence` slot. -/
theorem minconfidenceRow_plays {k : Nat} (hk : 2 ≤ k) (hkk : c_guard k + 3 ≤ k)
    (hk7 : c_guard k + 7 ≤ k)
    (hquine : proofSearch k (probe (inst (tauZoo k) .dupoc .dupoc)) = true)
    (hcim : proofSearch k (probe (inst (tauZoo k) .cimcic .dupoc)) = dupocColBit .cimcic)
    (hmir : proofSearch k (probe (inst (tauZoo k) .mirror .dupoc)) = dupocColBit .mirror)
    (hconf : proofSearch k (probe (inst (tauZoo k) .maxconfidence .dupoc))
      = dupocColBit .maxconfidence)
    (hcfP : ∃ N, eval N (.bot (inst (tauZoo k) .maxconfidence .dupoc))
      (.bot (inst (tauZoo k) .maxconfidence .dupoc)) (inst (tauZoo k) .maxconfidence .dupoc)
      = some Action.C)
    (hmirP : ∃ N, eval N (.bot (inst (tauZoo k) .dupoc .mirror))
      (.bot (inst (tauZoo k) .dupoc .mirror)) (inst (tauZoo k) .dupoc .mirror)
      = some (dupocRow .mirror))
    (hdmP : ∃ N, eval N (.bot (inst (tauZoo k) .dupoc .cimcic))
      (.bot (inst (tauZoo k) .dupoc .cimcic)) (inst (tauZoo k) .dupoc .cimcic)
      = some (dupocRow .cimcic)) :
    ∀ T, ∃ N, eval N (.bot (inst (tauZoo k) .minconfidence T))
              (.bot (inst (tauZoo k) .minconfidence T))
              (inst (tauZoo k) .minconfidence T) = some (minconfidenceRow T) := by
  have hcfP' : ∃ N, eval N (.bot (inst (tauZoo k) .dupoc .maxconfidence))
      (.bot (inst (tauZoo k) .dupoc .maxconfidence)) (inst (tauZoo k) .dupoc .maxconfidence)
      = some (dupocRow .maxconfidence) := by
    rw [inst_dupoc_maxconfidence_eq]; rw [inst_maxconfidence_dupoc_eq] at hcfP; exact hcfP
  have hD := dupocRow_plays hk hkk hk7 hquine hcim hmir hconf hcfP' hmirP hdmP
  intro T
  cases T with
  | dupoc => exact hcfP
  | maxconfidence => exact hcfP
  | minconfidence => rw [inst_minconfidence_quine]; exact inst_quine_plays hquine
  | just => exact searchProbe_plays_C _ _ (ps_probe_just_maxconfidence hkk hconf)
  | coop => rw [inst_minconfidence_eq_dupoc k .coop (by decide) (by decide) (by decide) (by decide)]; exact hD .coop
  | defect => rw [inst_minconfidence_eq_dupoc k .defect (by decide) (by decide) (by decide) (by decide)]; exact hD .defect
  | tftSim => rw [inst_minconfidence_eq_dupoc k .tftSim (by decide) (by decide) (by decide) (by decide)]; exact hD .tftSim
  | tftPf => rw [inst_minconfidence_eq_dupoc k .tftPf (by decide) (by decide) (by decide) (by decide)]; exact hD .tftPf
  | ebot => rw [inst_minconfidence_eq_dupoc k .ebot (by decide) (by decide) (by decide) (by decide)]; exact hD .ebot
  | obot => rw [inst_minconfidence_eq_dupoc k .obot (by decide) (by decide) (by decide) (by decide)]; exact hD .obot
  | guardian => rw [inst_minconfidence_eq_dupoc k .guardian (by decide) (by decide) (by decide) (by decide)]; exact hD .guardian
  | dbot => rw [inst_minconfidence_eq_dupoc k .dbot (by decide) (by decide) (by decide) (by decide)]; exact hD .dbot
  | cupod => rw [inst_minconfidence_eq_dupoc k .cupod (by decide) (by decide) (by decide) (by decide)]; exact hD .cupod
  | cupodTroll => rw [inst_minconfidence_eq_dupoc k .cupodTroll (by decide) (by decide) (by decide) (by decide)]; exact hD .cupodTroll
  | cimcic => rw [inst_minconfidence_eq_dupoc k .cimcic (by decide) (by decide) (by decide) (by decide)]; exact hD .cimcic
  | dimcid => rw [inst_minconfidence_eq_dupoc k .dimcid (by decide) (by decide) (by decide) (by decide)]; exact hD .dimcid
  | prudent => rw [inst_minconfidence_eq_dupoc k .prudent (by decide) (by decide) (by decide) (by decide)]; exact hD .prudent
  | mirror => rw [inst_minconfidence_eq_dupoc k .mirror (by decide) (by decide) (by decide) (by decide)]; exact hD .mirror

/-- **MinConfidenceBot's row** — the matrix-facing statement (`@[tau_row]`: validated
    by `Tau/Lint.lean`, exported to the app): unconditional at large `k`. -/
@[tau_row]
theorem minconfidenceRowSpec : RowSpec .minconfidence tauOrder minconfidenceRow := by
  obtain ⟨kL, hkL⟩ := ps_probe_inst_quine
  obtain ⟨kA, hkA⟩ := linear_log2_add_le 1 8
  obtain ⟨kM, hkM⟩ := ps_probe_inst_cimcic_dupoc
  obtain ⟨kP, hkP⟩ := dupoc_cimcic_plays_C
  obtain ⟨kX, hkX⟩ := ps_probe_mirror_dupoc
  obtain ⟨kY, hkY⟩ := dupoc_mirror_plays_C
  obtain ⟨kC, hkC⟩ := ps_probe_inst_maxconfidence_dupoc
  obtain ⟨kD, hkD⟩ := maxconfidence_dupoc_plays_C
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
  exact minconfidenceRow_plays hk2 hkk hk7 hquine hcim hmir hconf hcfP hmirP hdmP T

/-- **MinConfidenceBot's phase** — the MIN aggregator over its row: C iff no single
    hypothesis carrying at least θ of the signal has a D bit. Unconditional at
    large `k`. -/
theorem tauMinConfidence_phase :
    ∃ k₂, ∀ k, k₂ < k →
      ∀ θ (w : Tmpl → Nat) (opponent : Prog),
      (minMiss θ (tauOrder.map fun T => (w T, minconfidenceRow T)) = false →
        ∃ N, play N (MinConfidenceBotZ k w θ) opponent = some .C)
      ∧ (minMiss θ (tauOrder.map fun T => (w T, minconfidenceRow T)) = true →
        ∃ N, play N (MinConfidenceBotZ k w θ) opponent = some .D) := by
  obtain ⟨k₂, hrow⟩ := minconfidenceRowSpec
  refine ⟨k₂, fun k hk θ w opponent => ?_⟩
  have hbits := vecOf_bits (tauZoo k) .minconfidence w minconfidenceRow tauOrder (hrow k hk)
  exact minPlayer_phase_bits θ hbits opponent

/-- The readable form of the C-regime: every hypothesis with positive weight at
    least `θ` has a C bit. -/
theorem tauMinConfidence_phase' :
    ∃ k₂, ∀ k, k₂ < k →
      ∀ θ (w : Tmpl → Nat) (opponent : Prog),
      (∀ T ∈ tauOrder, 1 ≤ w T → θ ≤ w T → minconfidenceRow T = .C) →
        ∃ N, play N (MinConfidenceBotZ k w θ) opponent = some .C := by
  obtain ⟨k₂, h⟩ := tauMinConfidence_phase
  refine ⟨k₂, fun k hk θ w opponent hC => (h k hk θ w opponent).1 ?_⟩
  cases hmm : minMiss θ (tauOrder.map fun T => (w T, minconfidenceRow T)) with
  | false => rfl
  | true =>
      obtain ⟨p, hp, h1, hθ, ha⟩ := (minMiss_true_iff θ _).1 hmm
      obtain ⟨T, hT, rfl⟩ := List.mem_map.1 hp
      rw [hC T hT h1 hθ] at ha
      cases ha

/-- **MinConfidenceBot is the lift of NO template.** Every lift's play is
    `θ' ≤ bitMass w r` for its row `r` (`phase_of_bits`); the worst case is not, for
    ANY `r` and `θ'`: on the signals `2·δ_defect`, `δ_defect + δ_dbot`, `2·δ_dbot`
    (both slots D in `minconfidenceRow`) MinConfidenceBot plays D, C, D at `θ = 2` —
    a lone credible defector vetoes, two incredible ones do not — and a threshold of
    a linear mass cannot: agreeing on the first two forces the middle mass, the
    average of the outer two, to clear a threshold neither outer one does. -/
theorem minconfidence_not_linear :
    ¬ ∃ (θ' : Nat) (r : Tmpl → Action), ∀ w : Tmpl → Nat,
      decide (θ' ≤ bitMass w r tauOrder)
        = !(minMiss 2 (tauOrder.map fun T => (w T, minconfidenceRow T))) := by
  rintro ⟨θ', r, h⟩
  have h1 := h (fun T => if T = .defect then 2 else 0)
  have h2 := h (fun T => if T = .defect ∨ T = .dbot then 1 else 0)
  have h3 := h (fun T => if T = .dbot then 2 else 0)
  have e1 : minMiss 2 (tauOrder.map fun T =>
      ((fun T : Tmpl => if T = .defect then 2 else 0) T, minconfidenceRow T)) = true := by decide
  have e2 : minMiss 2 (tauOrder.map fun T =>
      ((fun T : Tmpl => if T = .defect ∨ T = .dbot then 1 else 0) T, minconfidenceRow T)) = false := by
    decide
  have e3 : minMiss 2 (tauOrder.map fun T =>
      ((fun T : Tmpl => if T = .dbot then 2 else 0) T, minconfidenceRow T)) = true := by decide
  rw [e1] at h1; rw [e2] at h2; rw [e3] at h3
  simp only [bitMass, tauOrder, List.map, massOf, decide_eq_true_eq, decide_eq_false_iff_not,
    Bool.not_true, Bool.not_false] at h1 h2 h3
  simp at h1 h2 h3
  cases hd : r .defect <;> cases hb : r .dbot <;> simp [hd, hb] at h1 h2 h3 <;> omega

end PD.Tau
