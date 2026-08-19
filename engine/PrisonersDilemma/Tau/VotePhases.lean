import PrisonersDilemma.Tau.InstCerts

/-!
# Tau/VotePhases — α-phase theorems for the refined Def-4 zoo (DSL interface, Phase 5)

Each bot's phase theorem is a two-step corollary of the uniform machinery: supply a
`VoteBits` and compute the mass. Since the InstCerts rewiring (2026-08-18), every
bits proof is a COLUMN READ: each slot cites the inst-native column theorem
(`ps_probe_inst_coop`/`_defect`/`_dupoc`, or the behavioral `inst_coop_plays`) at
its hypothesis index — one quantified lemma per question the bot asks, instead of
six per-instance citations. Weights are a function `w : Tmpl → Nat`.

**The headline correction stands unchanged**: τ(EBot)'s bits are Coop 0, Defect 0,
TFTSim 1, TFTPf 1, Dupoc 1, EBot 0 — mass `w .tftSim + w .tftPf + w .dupoc`, a
ONE-SIDED boundary (the retracted crowd-exploiter's window does not exist). The
three cooperators share `w .coop + w .tftSim + w .tftPf + w .dupoc`; TauDupoc's mass
honestly EXCLUDES `w .ebot` (the floor cell).
-/

open PD PD.BaseTheorems

namespace PD.Tau

/-! ## Mass-arithmetic helpers -/

@[simp] theorem massOf_ifC (w : Nat) :
    (if (Action.C == Action.C) = true then w else 0) = w := if_pos rfl

@[simp] theorem massOf_ifD (w : Nat) :
    (if (Action.D == Action.C) = true then w else 0) = 0 :=
  if_neg (by decide)

/-! ## The constants -/

theorem coopBits (k : Nat) (w : Tmpl → Nat) :
    VoteBits (vecOf (zoo6 k) .coop w order6)
      [(w .coop, .C), (w .defect, .C), (w .tftSim, .C),
       (w .tftPf, .C), (w .dupoc, .C), (w .ebot, .C)] :=
  .cons ⟨1, rfl⟩ (.cons ⟨1, rfl⟩ (.cons ⟨1, rfl⟩ (.cons ⟨1, rfl⟩
    (.cons ⟨1, rfl⟩ (.cons ⟨1, rfl⟩ .nil)))))

/-- **τ(CooperateBot)**: signal-blind — its whole mass cooperates. -/
theorem tauCooperate_phase (k : Nat) (w : Tmpl → Nat) (θ : Nat) (opponent : Prog) :
    (θ ≤ w .coop + (w .defect + (w .tftSim + (w .tftPf + (w .dupoc + (w .ebot + 0))))) →
      ∃ N, play N (TauBotZ k .coop w θ) opponent = some .C)
    ∧ (¬ θ ≤ w .coop + (w .defect + (w .tftSim + (w .tftPf + (w .dupoc + (w .ebot + 0))))) →
      ∃ N, play N (TauBotZ k .coop w θ) opponent = some .D) := by
  have h := tauPlayer_phase_bits θ (coopBits k w) opponent
  simpa [massOf, TauBotZ] using h

theorem defectBits (k : Nat) (w : Tmpl → Nat) :
    VoteBits (vecOf (zoo6 k) .defect w order6)
      [(w .coop, .D), (w .defect, .D), (w .tftSim, .D),
       (w .tftPf, .D), (w .dupoc, .D), (w .ebot, .D)] :=
  .cons ⟨1, rfl⟩ (.cons ⟨1, rfl⟩ (.cons ⟨1, rfl⟩ (.cons ⟨1, rfl⟩
    (.cons ⟨1, rfl⟩ (.cons ⟨1, rfl⟩ .nil)))))

/-- **τ(DefectBot)**: zero cooperation mass. -/
theorem tauDefect_phase (k : Nat) (w : Tmpl → Nat) (θ : Nat) (opponent : Prog) :
    (θ = 0 → ∃ N, play N (TauBotZ k .defect w θ) opponent = some .C)
    ∧ (θ ≠ 0 → ∃ N, play N (TauBotZ k .defect w θ) opponent = some .D) := by
  have h := tauPlayer_phase_bits θ (defectBits k w) opponent
  simp only [massOf, massOf_ifD, TauBotZ] at h ⊢
  exact ⟨fun hθ => h.1 (by omega), fun hθ => h.2 (by omega)⟩

/-! ## τ(EBot) — the corrected bot, ONE-SIDED boundary -/

theorem eBits {k : Nat} (hk : 2 ≤ k) (hkk : c_guard k + 3 ≤ k) (h6 : 6 ≤ k)
    (w : Tmpl → Nat) :
    VoteBits (vecOf (zoo6 k) .ebot w order6)
      [(w .coop, .D), (w .defect, .D), (w .tftSim, .C),
       (w .tftPf, .C), (w .dupoc, .C), (w .ebot, .D)] :=
  -- τ(EBot)'s entry at hypothesis T is the cascade over T's δ_D and δ_C column
  -- bits, so the whole table is TWO column reads.
  let bD := ps_probe_inst_defect (k := k) hk
  let bC := ps_probe_inst_coop hk hkk h6
  .cons (eδ_plays_D_of_exploit _ _ (bD .coop))
    (.cons (eδ_plays_D_of_both_false _ _ (bD .defect) (bC .defect))
      (.cons (eδ_plays_C _ _ (bD .tftSim) (bC .tftSim))
        (.cons (eδ_plays_C _ _ (bD .tftPf) (bC .tftPf))
          (.cons (eδ_plays_C _ _ (bD .dupoc) (bC .dupoc))
            (.cons (eδ_plays_D_of_both_false _ _ (bD .ebot) (bC .ebot)) .nil)))))

/-- **τ(EBot) α-phase theorem — the ONE-SIDED boundary** `θ ≤ wTs + wTp + wL`. -/
theorem tauEBot_phase {k : Nat} (hk : 2 ≤ k) (hkk : c_guard k + 3 ≤ k) (h6 : 6 ≤ k)
    (θ : Nat) (w : Tmpl → Nat) (opponent : Prog) :
    (θ ≤ w .tftSim + (w .tftPf + w .dupoc) →
      ∃ N, play N (TauBotZ k .ebot w θ) opponent = some .C)
    ∧ (¬ θ ≤ w .tftSim + (w .tftPf + w .dupoc) →
      ∃ N, play N (TauBotZ k .ebot w θ) opponent = some .D) := by
  have h := tauPlayer_phase_bits θ (eBits hk hkk h6 w) opponent
  simp only [massOf, massOf_ifC, massOf_ifD, TauBotZ] at h ⊢
  simpa using h

/-! ## The three cooperators — shared boundary `θ ≤ wC + wTs + wTp + wL` -/

theorem tftPfBits {k : Nat} (hk : 2 ≤ k) (hkk : c_guard k + 3 ≤ k) (h6 : 6 ≤ k)
    (w : Tmpl → Nat) :
    VoteBits (vecOf (zoo6 k) .tftPf w order6)
      [(w .coop, .C), (w .defect, .D), (w .tftSim, .C),
       (w .tftPf, .C), (w .dupoc, .C), (w .ebot, .D)] :=
  -- τ(TFTPf)'s entry at T probes T's δ_C column bit: ONE column read.
  let bC := ps_probe_inst_coop hk hkk h6
  .cons (probeSearchδ_plays_C _ _ (bC .coop))
    (.cons (probeSearchδ_plays_D _ _ (bC .defect))
      (.cons (probeSearchδ_plays_C _ _ (bC .tftSim))
        (.cons (probeSearchδ_plays_C _ _ (bC .tftPf))
          (.cons (probeSearchδ_plays_C _ _ (bC .dupoc))
            (.cons (probeSearchδ_plays_D _ _ (bC .ebot)) .nil)))))

/-- **τ(TitForTatBot), prover variant.** -/
theorem tauTFTPf_phase {k : Nat} (hk : 2 ≤ k) (hkk : c_guard k + 3 ≤ k) (h6 : 6 ≤ k)
    (θ : Nat) (w : Tmpl → Nat) (opponent : Prog) :
    (θ ≤ w .coop + (w .tftSim + (w .tftPf + w .dupoc)) →
      ∃ N, play N (TauBotZ k .tftPf w θ) opponent = some .C)
    ∧ (¬ θ ≤ w .coop + (w .tftSim + (w .tftPf + w .dupoc)) →
      ∃ N, play N (TauBotZ k .tftPf w θ) opponent = some .D) := by
  have h := tauPlayer_phase_bits θ (tftPfBits hk hkk h6 w) opponent
  simp only [massOf, massOf_ifC, massOf_ifD, TauBotZ] at h ⊢
  simpa using h

theorem tftSimBits {k : Nat} (hk : 2 ≤ k) (hkk : c_guard k + 3 ≤ k) (h6 : 6 ≤ k)
    (w : Tmpl → Nat) :
    VoteBits (vecOf (zoo6 k) .tftSim w order6)
      [(w .coop, .C), (w .defect, .D), (w .tftSim, .C),
       (w .tftPf, .C), (w .dupoc, .C), (w .ebot, .D)] :=
  -- τ(TFTSim)'s entry at T COPIES T's δ_C-column TRUE play: the behavioral column.
  let pC := inst_coop_plays hk hkk h6
  .cons (tftSimδ_plays _ _ (pC .coop))
    (.cons (tftSimδ_plays _ _ (pC .defect))
      (.cons (tftSimδ_plays _ _ (pC .tftSim))
        (.cons (tftSimδ_plays _ _ (pC .tftPf))
          (.cons (tftSimδ_plays _ _ (pC .dupoc))
            (.cons (tftSimδ_plays _ _ (pC .ebot)) .nil)))))

/-- **τ(TitForTatBot), behavioral variant** — same boundary, far smaller budget. -/
theorem tauTFTSim_phase {k : Nat} (hk : 2 ≤ k) (hkk : c_guard k + 3 ≤ k) (h6 : 6 ≤ k)
    (θ : Nat) (w : Tmpl → Nat) (opponent : Prog) :
    (θ ≤ w .coop + (w .tftSim + (w .tftPf + w .dupoc)) →
      ∃ N, play N (TauBotZ k .tftSim w θ) opponent = some .C)
    ∧ (¬ θ ≤ w .coop + (w .tftSim + (w .tftPf + w .dupoc)) →
      ∃ N, play N (TauBotZ k .tftSim w θ) opponent = some .D) := by
  have h := tauPlayer_phase_bits θ (tftSimBits hk hkk h6 w) opponent
  simp only [massOf, massOf_ifC, massOf_ifD, TauBotZ] at h ⊢
  simpa using h

/-! ## τ(DupocBot) — Löb-gated, boundary excludes `w .ebot` (the floor) -/

theorem dupocBits {k : Nat} (hk : 2 ≤ k) (hkk : c_guard k + 3 ≤ k)
    (hk7 : c_guard k + 7 ≤ k)
    (hquine : proofSearch k (probe (inst (zoo6 k) .dupoc .dupoc)) = true)
    (w : Tmpl → Nat) :
    VoteBits (vecOf (zoo6 k) .dupoc w order6)
      [(w .coop, .C), (w .defect, .D), (w .tftSim, .C),
       (w .tftPf, .C), (w .dupoc, .C), (w .ebot, .D)] :=
  -- τ(Dupoc)'s entry at T probes T's δ_L column bit ("does T, seeing ME,
  -- cooperate?"): one column read, plus the quine at the diagonal. The EBot slot
  -- is THE FLOOR: `dupocColBit .ebot = false` although the instance truly
  -- cooperates (the Gödelian pair in InstCerts).
  let bL := ps_probe_inst_dupoc hk hkk hk7 hquine
  .cons (probeSearchδ_plays_C _ _ (bL .coop))
    (.cons (probeSearchδ_plays_D _ _ (bL .defect))
      (.cons (probeSearchδ_plays_C _ _ (bL .tftSim))
        (.cons (probeSearchδ_plays_C _ _ (bL .tftPf))
          (.cons (inst_quine_plays hquine)
            (.cons (probeSearchδ_plays_D _ _ (bL .ebot)) .nil)))))

/-- **τ(DupocBot) α-phase theorem** — Löb-gated; the mass excludes `w .ebot`. -/
theorem tauDupoc_phase :
    ∃ k₂, ∀ k, k₂ < k → ∀ θ (w : Tmpl → Nat) (opponent : Prog),
      (θ ≤ w .coop + (w .tftSim + (w .tftPf + w .dupoc)) →
        ∃ N, play N (TauBotZ k .dupoc w θ) opponent = some .C)
      ∧ (¬ θ ≤ w .coop + (w .tftSim + (w .tftPf + w .dupoc)) →
        ∃ N, play N (TauBotZ k .dupoc w θ) opponent = some .D) := by
  obtain ⟨kL, hkL⟩ := ps_probe_quine
  obtain ⟨kA, hkA⟩ := linear_log2_add_le 1 8
  refine ⟨max kL kA, fun k hk θ w opponent => ?_⟩
  have hquine := hkL k (lt_of_le_of_lt (Nat.le_max_left _ _) hk)
  have hkA' : 1 * Nat.log2 k + 8 ≤ k :=
    hkA k (Nat.le_of_lt (lt_of_le_of_lt (Nat.le_max_right _ _) hk))
  have hk2 : 2 ≤ k := by omega
  have hkk : c_guard k + 3 ≤ k := by simp only [c_guard, numCost]; omega
  have hk7 : c_guard k + 7 ≤ k := by simp only [c_guard, numCost]; omega
  have h := tauPlayer_phase_bits θ (dupocBits hk2 hkk hk7 hquine w) opponent
  simp only [massOf, massOf_ifC, massOf_ifD, TauBotZ] at h ⊢
  simpa using h

end PD.Tau
