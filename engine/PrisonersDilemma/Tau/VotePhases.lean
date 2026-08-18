import PrisonersDilemma.Tau.Spec

/-!
# Tau/VotePhases — α-phase theorems for the refined Def-4 zoo (DSL interface, Phase 5)

Each bot's phase theorem is a two-step corollary of the uniform machinery: supply a
`VoteBits` (what every entry of the COMPILED vector plays — the entries are
`rfl`-equal to the hand-written closure by Gate D1, so the Phase-4 entry-play lemmas
apply verbatim) and compute the mass. Weights are a function `w : Tmpl → Nat`, per
the DSL interface.

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
       (w .tftPf, .C), (w .dupoc, .C), (w .ebot, .D)] := by
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
  -- the compiled entries are rfl-equal to the eδ-instances (Gate D1), so the
  -- Phase-4 entry-play lemmas close each slot directly
  exact .cons (eδ_plays_D_of_exploit _ _ bCoop)
    (.cons (eδ_plays_D_of_both_false _ _ bDef bDef)
      (.cons (eδ_plays_C _ _ bSimD bSimC)
        (.cons (eδ_plays_C _ _ bSchD bSchC)
          (.cons (eδ_plays_C _ _ bSchD bSchC)
            (.cons (eδ_plays_D_of_both_false _ _ bEDef bECoop) .nil)))))

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
  .cons (probeSearchδ_plays_C _ _ (ps_probe_coop hk))
    (.cons (probeSearchδ_plays_D _ _ (ps_probe_defect k))
      (.cons (probeSearchδ_plays_C _ _ (ps_probe_simOfCoop h6))
        (.cons (probeSearchδ_plays_C _ _ (ps_probe_searchOfCoop hk hkk))
          (.cons (probeSearchδ_plays_C _ _ (ps_probe_searchOfCoop hk hkk))
            (.cons (probeSearchδ_plays_D _ _ (ps_probe_eOfCoop_false hk k)) .nil)))))

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
       (w .tftPf, .C), (w .dupoc, .C), (w .ebot, .D)] := by
  refine .cons (tftSimδ_plays _ _ ⟨1, rfl⟩)
    (.cons (tftSimδ_plays _ _ ⟨1, rfl⟩)
      (.cons (tftSimδ_plays _ _ (entry_C_of_interp (Pf_sound _ _ (pf_probe_simOfCoop h6))))
        (.cons (tftSimδ_plays _ _
            (entry_C_of_interp (Pf_sound _ _ (pf_probe_searchOfCoop hk hkk))))
          (.cons (tftSimδ_plays _ _
              (entry_C_of_interp (Pf_sound _ _ (pf_probe_searchOfCoop hk hkk))))
            (.cons (tftSimδ_plays _ _ ?_) .nil)))))
  -- The compiled entry displays in `instGo` form, so state the play against the
  -- NAMED instance explicitly and let defeq (Gate D1) bridge the two.
  have hb : proofSearch k (probe tauCoopδ) = true := ps_probe_coop hk
  have hplay : eval 3 (.bot (eOfCoopδ k)) (.bot (eOfCoopδ k)) (eOfCoopδ k)
      = some Action.D := by
    rw [eOfCoopδ, eδ, eval, probe_subst, hb]; rfl
  exact entry_D_of_not_interp ⟨3, Action.D, hplay⟩ (interp_probe_eOfCoop_false hk)

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
    (hquine : proofSearch k (probe (TauDupocδ k)) = true) (w : Tmpl → Nat) :
    VoteBits (vecOf (zoo6 k) .dupoc w order6)
      [(w .coop, .C), (w .defect, .D), (w .tftSim, .C),
       (w .tftPf, .C), (w .dupoc, .C), (w .ebot, .D)] := by
  refine .cons (probeSearchδ_plays_C _ _ (ps_probe_coop hk))
    (.cons (probeSearchδ_plays_D _ _ (ps_probe_defect k))
      (.cons (probeSearchδ_plays_C _ _ (ps_probe_simOfSearch hk hk7))
        (.cons (probeSearchδ_plays_C _ _ (ps_probe_searchOfSearch hk hkk))
          (.cons ?_
            (.cons (probeSearchδ_plays_D _ _ (ps_probe_eOfSearch_false (le_refl k)))
              .nil)))))
  -- The quine entry: running `.bot`-framed, subst closes `.self` to the wrapped
  -- quine, whose guard IS `probe (TauDupocδ k)` — the Löb fixpoint bit. Stated
  -- against the NAMED quine; defeq (Gate D1) bridges to the compiled form.
  have h : proofSearch k ((Formula.plays Prog.self Prog.self Action.C).subst
      (.bot (TauDupocδ k)) (.bot (TauDupocδ k))) = true := hquine
  have hq : eval 2 (.bot (TauDupocδ k)) (.bot (TauDupocδ k)) (TauDupocδ k)
      = some Action.C := by
    rw [TauDupocδ, eval] at *
    rw [h]
    rfl
  exact ⟨2, hq⟩

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
