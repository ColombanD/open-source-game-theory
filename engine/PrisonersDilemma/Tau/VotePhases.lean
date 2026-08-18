import PrisonersDilemma.Tau.Vectors

/-!
# Tau/VotePhases — α-phase theorems for the refined Def-4 zoo (2026-08-18)

Each bot's phase theorem is now a two-step corollary of the UNIFORM
`tauPlayer_phase`: supply a `VoteAllVals` (what every entry plays) and compute the
vector's `voteMass`. No per-bot induction, no per-bot peel.

**The headline correction.** τ(EBot)'s bits are Coop 0, Defect 0, TFTSim 1, TFTPf 1,
Dupoc 1, EBot 0 — mass `wTs + wTp + wL`, a ONE-SIDED boundary. The retracted
crowd-exploiter had a cooperation WINDOW (`wC < θ ≤ wC+wTs+wTp+wL`, defecting at both
α-extremes); that shape belonged to the per-stage vote, not to the lift of EBot.

The three cooperators keep the boundary the milestone-1 layer found,
`θ ≤ wC + wTs + wTp + wL` — TauDupoc's mass still honestly EXCLUDES `wE` (the floor
cell), which is a good regression check that the modality move did not disturb the
Gödelian content.
-/

open PD PD.BaseTheorems

namespace PD.Tau

/-! ## Mass-arithmetic helpers

`massOf` guards each weight with `a == Action.C`; these two close those `if`s so the
per-bot masses reduce to plain sums. -/

@[simp] theorem massOf_ifC (w : Nat) :
    (if (Action.C == Action.C) = true then w else 0) = w := if_pos rfl

@[simp] theorem massOf_ifD (w : Nat) :
    (if (Action.D == Action.C) = true then w else 0) = 0 :=
  if_neg (by decide)

/-! ## The constants -/

theorem coopVec_bits (wC wD wTs wTp wL wE : Nat) :
    VoteBits (coopVec wC wD wTs wTp wL wE)
      [(wC, .C), (wD, .C), (wTs, .C), (wTp, .C), (wL, .C), (wE, .C)] := by
  exact .cons ⟨1, rfl⟩ (.cons ⟨1, rfl⟩ (.cons ⟨1, rfl⟩ (.cons ⟨1, rfl⟩
    (.cons ⟨1, rfl⟩ (.cons ⟨1, rfl⟩ .nil)))))

/-- **τ(CooperateBot)**: signal-blind — its whole mass cooperates, so it plays C for
    any threshold within the total weight. The lift of a constant is constant. -/
theorem tauCooperate_phase (wC wD wTs wTp wL wE θ : Nat) (opponent : Prog) :
    (θ ≤ wC + (wD + (wTs + (wTp + (wL + (wE + 0))))) →
      ∃ N, play N (TauCooperate wC wD wTs wTp wL wE θ) opponent = some .C)
    ∧ (¬ θ ≤ wC + (wD + (wTs + (wTp + (wL + (wE + 0))))) →
      ∃ N, play N (TauCooperate wC wD wTs wTp wL wE θ) opponent = some .D) := by
  have h := tauPlayer_phase_bits θ (coopVec_bits wC wD wTs wTp wL wE) opponent
  simpa [massOf, TauCooperate] using h

theorem defectVec_bits (wC wD wTs wTp wL wE : Nat) :
    VoteBits (defectVec wC wD wTs wTp wL wE)
      [(wC, .D), (wD, .D), (wTs, .D), (wTp, .D), (wL, .D), (wE, .D)] := by
  exact .cons ⟨1, rfl⟩ (.cons ⟨1, rfl⟩ (.cons ⟨1, rfl⟩ (.cons ⟨1, rfl⟩
    (.cons ⟨1, rfl⟩ (.cons ⟨1, rfl⟩ .nil)))))

/-- **τ(DefectBot)**: zero cooperation mass — it plays D unless the threshold is 0. -/
theorem tauDefect_phase (wC wD wTs wTp wL wE θ : Nat) (opponent : Prog) :
    (θ = 0 → ∃ N, play N (TauDefect wC wD wTs wTp wL wE θ) opponent = some .C)
    ∧ (θ ≠ 0 → ∃ N, play N (TauDefect wC wD wTs wTp wL wE θ) opponent = some .D) := by
  have h := tauPlayer_phase_bits θ (defectVec_bits wC wD wTs wTp wL wE) opponent
  simp only [massOf, TauDefect] at h ⊢
  exact ⟨fun hθ => h.1 (by simp [hθ]), fun hθ => h.2 (by simp; omega)⟩

/-! ## τ(EBot) — THE corrected bot

Each entry is EBot's whole exploiter cascade at point mass on one hypothesis, and the
vote runs ONCE over those six compound decisions. Bits: exploits the cooperator
(Coop 0), gains nothing from the defector (Defect 0), reciprocates both TFTs and Dupoc
(1, 1, 1), and — lacking base EBot's non-liftable Mirror branch — defects against
itself (EBot 0).

**Boundary `θ ≤ wTs + wTp + wL`: ONE-SIDED, no window.** The retracted crowd-exploiter
had a cooperation window `wC < θ ≤ wC+wTs+wTp+wL` and defected at both α-extremes; that
shape belonged to its per-stage vote, not to any lift of EBot. -/

theorem eVec_bits {k : Nat} (hk : 2 ≤ k) (hkk : c_guard k + 3 ≤ k) (h6 : 6 ≤ k)
    (wC wD wTs wTp wL wE : Nat) :
    VoteBits (eVec k wC wD wTs wTp wL wE)
      [(wC, .D), (wD, .D), (wTs, .C), (wTp, .C), (wL, .C), (wE, .D)] := by
  have bCoop : proofSearch k (probe tauCoopδ) = true := ps_probe_coop hk
  have bDef : proofSearch k (probe tauDefectδ) = false := ps_probe_defect k
  have bSimD : proofSearch k (probe simOfDefectδ) = false := ps_probe_simOfDefect k
  have bSimC : proofSearch k (probe simOfCoopδ) = true := ps_probe_simOfCoop h6
  have bSchD : proofSearch k (probe (searchOfDefectδ k)) = false :=
    ps_probe_searchOfDefect k k
  have bSchC : proofSearch k (probe (searchOfCoopδ k)) = true :=
    ps_probe_searchOfCoop hk hkk
  have bEDef : proofSearch k (probe (eOfDefectδ k)) = false := ps_probe_eOfDefect k k
  have bECoop : proofSearch k (probe (eOfCoopδ k)) = false := ps_probe_eOfCoop_false hk k
  exact .cons (eδ_plays_D_of_exploit _ _ bCoop)
    (.cons (eδ_plays_D_of_both_false _ _ bDef bDef)
      (.cons (eδ_plays_C _ _ bSimD bSimC)
        (.cons (eδ_plays_C _ _ bSchD bSchC)
          (.cons (eδ_plays_C _ _ bSchD bSchC)
            (.cons (eδ_plays_D_of_both_false _ _ bEDef bECoop) .nil)))))

/-- **τ(EBot) α-phase theorem — the ONE-SIDED boundary.** -/
theorem tauEBot_phase {k : Nat} (hk : 2 ≤ k) (hkk : c_guard k + 3 ≤ k) (h6 : 6 ≤ k)
    (θ wC wD wTs wTp wL wE : Nat) (opponent : Prog) :
    (θ ≤ wTs + (wTp + wL) →
      ∃ N, play N (TauEBot k θ wC wD wTs wTp wL wE) opponent = some .C)
    ∧ (¬ θ ≤ wTs + (wTp + wL) →
      ∃ N, play N (TauEBot k θ wC wD wTs wTp wL wE) opponent = some .D) := by
  have h := tauPlayer_phase_bits θ (eVec_bits hk hkk h6 wC wD wTs wTp wL wE) opponent
  simp only [massOf, TauEBot] at h ⊢
  simpa using h

/-! ## The three cooperators

All three share the boundary `θ ≤ wC + wTs + wTp + wL`, at different BUDGET
thresholds — the prover/behavioral split is a budget-phase gap, not an α-gap.
TauDupoc's mass honestly EXCLUDES `wE`: `E(δ_L)` really cooperates, but only through a
failed exploit-search, so no ≤k certificate exists and its entry's guard reads 0. That
the boundary survived the move from a provability-vote to an action-vote is the
regression check that the Gödelian content sits where the corrected definition says it
does — inside the entry, not at the vote. -/

theorem tftPfVec_bits {k : Nat} (hk : 2 ≤ k) (hkk : c_guard k + 3 ≤ k) (h6 : 6 ≤ k)
    (wC wD wTs wTp wL wE : Nat) :
    VoteBits (tftPfVec k wC wD wTs wTp wL wE)
      [(wC, .C), (wD, .D), (wTs, .C), (wTp, .C), (wL, .C), (wE, .D)] :=
  .cons (probeSearchδ_plays_C _ _ (ps_probe_coop hk))
    (.cons (probeSearchδ_plays_D _ _ (ps_probe_defect k))
      (.cons (probeSearchδ_plays_C _ _ (ps_probe_simOfCoop h6))
        (.cons (probeSearchδ_plays_C _ _ (ps_probe_searchOfCoop hk hkk))
          (.cons (probeSearchδ_plays_C _ _ (ps_probe_searchOfCoop hk hkk))
            (.cons (probeSearchδ_plays_D _ _ (ps_probe_eOfCoop_false hk k)) .nil)))))

/-- **τ(TitForTatBot), prover variant.** -/
theorem tauTFTPf_phase {k : Nat} (hk : 2 ≤ k) (hkk : c_guard k + 3 ≤ k) (h6 : 6 ≤ k)
    (θ wC wD wTs wTp wL wE : Nat) (opponent : Prog) :
    (θ ≤ wC + (wTs + (wTp + wL)) →
      ∃ N, play N (TauTFTPf k θ wC wD wTs wTp wL wE) opponent = some .C)
    ∧ (¬ θ ≤ wC + (wTs + (wTp + wL)) →
      ∃ N, play N (TauTFTPf k θ wC wD wTs wTp wL wE) opponent = some .D) := by
  have h := tauPlayer_phase_bits θ (tftPfVec_bits hk hkk h6 wC wD wTs wTp wL wE) opponent
  simp only [massOf, TauTFTPf] at h ⊢
  simpa using h

theorem tftSimVec_bits {k : Nat} (hk : 2 ≤ k) (hkk : c_guard k + 3 ≤ k) (h6 : 6 ≤ k)
    (wC wD wTs wTp wL wE : Nat) :
    VoteBits (tftSimVec k wC wD wTs wTp wL wE)
      [(wC, .C), (wD, .D), (wTs, .C), (wTp, .C), (wL, .C), (wE, .D)] := by
  -- every entry is `tftSimδ H` for a hypothesis `H` whose own play is already known:
  -- the behavioral read simply copies it (`tftSimδ_plays`).
  refine .cons (tftSimδ_plays _ _ ⟨1, rfl⟩)
    (.cons (tftSimδ_plays _ _ ⟨1, rfl⟩)
      (.cons (tftSimδ_plays _ _ (entry_C_of_interp (Pf_sound _ _ (pf_probe_simOfCoop h6))))
        (.cons (tftSimδ_plays _ _
            (entry_C_of_interp (Pf_sound _ _ (pf_probe_searchOfCoop hk hkk))))
          (.cons (tftSimδ_plays _ _
              (entry_C_of_interp (Pf_sound _ _ (pf_probe_searchOfCoop hk hkk))))
            (.cons (tftSimδ_plays _ _ ?_) .nil)))))
  -- the EBot hypothesis DEFECTS (it exploits a cooperator), so this entry copies D
  exact entry_D_of_not_interp ⟨3, Action.D, by
      have hb : proofSearch k (probe tauCoopδ) = true := ps_probe_coop hk
      rw [eOfCoopδ, eδ, eval, probe_subst, hb]; rfl⟩
    (interp_probe_eOfCoop_false hk)

/-- **τ(TitForTatBot), behavioral variant.** Same boundary as the prover variant,
    reached at a far smaller budget. -/
theorem tauTFTSim_phase {k : Nat} (hk : 2 ≤ k) (hkk : c_guard k + 3 ≤ k) (h6 : 6 ≤ k)
    (θ wC wD wTs wTp wL wE : Nat) (opponent : Prog) :
    (θ ≤ wC + (wTs + (wTp + wL)) →
      ∃ N, play N (TauTFTSim k θ wC wD wTs wTp wL wE) opponent = some .C)
    ∧ (¬ θ ≤ wC + (wTs + (wTp + wL)) →
      ∃ N, play N (TauTFTSim k θ wC wD wTs wTp wL wE) opponent = some .D) := by
  have h := tauPlayer_phase_bits θ
    (tftSimVec_bits hk hkk h6 wC wD wTs wTp wL wE) opponent
  simp only [massOf, TauTFTSim] at h ⊢
  simpa using h

/-- τ(DupocBot)'s bits, past the Löb threshold. The Dupoc entry is the `.self` quine
    (bounded Löb closes it AT the probing budget); the EBot entry is the floor cell. -/
theorem dupocVec_bits {k : Nat} (hk : 2 ≤ k) (hkk : c_guard k + 3 ≤ k)
    (hk7 : c_guard k + 7 ≤ k)
    (hquine : proofSearch k (probe (TauDupocδ k)) = true)
    (wC wD wTs wTp wL wE : Nat) :
    VoteBits (dupocVec k wC wD wTs wTp wL wE)
      [(wC, .C), (wD, .D), (wTs, .C), (wTp, .C), (wL, .C), (wE, .D)] := by
  refine .cons (probeSearchδ_plays_C _ _ (ps_probe_coop hk))
    (.cons (probeSearchδ_plays_D _ _ (ps_probe_defect k))
      (.cons (probeSearchδ_plays_C _ _ (ps_probe_simOfSearch hk hk7))
        (.cons (probeSearchδ_plays_C _ _ (ps_probe_searchOfSearch hk hkk))
          (.cons ?_
            (.cons (probeSearchδ_plays_D _ _ (ps_probe_eOfSearch_false (le_refl k)))
              .nil)))))
  -- The quine entry. `TauDupocδ k` is a `.search` on its OWN `.self`-probe, so it is
  -- not a frozen `.bot`-probe of another term and `probeSearchδ_plays_C` does not
  -- apply: running `.bot`-framed, `subst` closes `.self` to the bot-wrapped quine,
  -- which IS `probe (TauDupocδ k)` definitionally — the Löb fixpoint whose bit
  -- `ps_probe_quine` supplies at the probing budget itself.
  refine ⟨2, ?_⟩
  have h : proofSearch k ((Formula.plays Prog.self Prog.self Action.C).subst
      (.bot (TauDupocδ k)) (.bot (TauDupocδ k))) = true := hquine
  rw [TauDupocδ, eval] at *
  rw [h]
  rfl

/-- **τ(DupocBot) α-phase theorem** — Löb-gated, boundary excludes `wE` (the floor). -/
theorem tauDupoc_phase :
    ∃ k₂, ∀ k, k₂ < k → ∀ θ wC wD wTs wTp wL wE (opponent : Prog),
      (θ ≤ wC + (wTs + (wTp + wL)) →
        ∃ N, play N (TauDupoc k θ wC wD wTs wTp wL wE) opponent = some .C)
      ∧ (¬ θ ≤ wC + (wTs + (wTp + wL)) →
        ∃ N, play N (TauDupoc k θ wC wD wTs wTp wL wE) opponent = some .D) := by
  obtain ⟨kL, hkL⟩ := ps_probe_quine
  obtain ⟨kA, hkA⟩ := linear_log2_add_le 1 8
  refine ⟨max kL kA, fun k hk θ wC wD wTs wTp wL wE opponent => ?_⟩
  have hquine := hkL k (lt_of_le_of_lt (Nat.le_max_left _ _) hk)
  have hkA' : 1 * Nat.log2 k + 8 ≤ k :=
    hkA k (Nat.le_of_lt (lt_of_le_of_lt (Nat.le_max_right _ _) hk))
  have hk2 : 2 ≤ k := by omega
  have hkk : c_guard k + 3 ≤ k := by simp only [c_guard, numCost]; omega
  have hk7 : c_guard k + 7 ≤ k := by simp only [c_guard, numCost]; omega
  have h := tauPlayer_phase_bits θ
    (dupocVec_bits hk2 hkk hk7 hquine wC wD wTs wTp wL wE) opponent
  simp only [massOf, TauDupoc] at h ⊢
  simpa using h

end PD.Tau