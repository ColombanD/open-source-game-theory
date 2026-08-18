import PrisonersDilemma.Tau.VotePhases

/-!
# Theorems/Tau/VoteMatrix — the refined Def-4 outcome matrix (DSL interface, Phase 5)

Ordered outcomes of the six-template zoo, every cell a corollary of the α-phase
theorems (tau players are `.opp`-free, hence extensionally constant, so the matrix is
the product of the play vector with itself). Players are `TauBotZ k A w θ` — the
compiled DSL interface, weights `w : Tmpl → Nat`.

**Two α-regimes, differing per bot.** The cooperators share
`θ ≤ w .coop + w .tftSim + w .tftPf + w .dupoc`; τ(EBot)'s boundary is
`θ ≤ w .tftSim + w .tftPf + w .dupoc` — strictly lower (it EXCLUDES the cooperator
weight EBot exploits), and ONE-SIDED (no window). The band between them is where the
exploiter is observable (`outcome_TauTFTPf_vs_TauEBot_band`).
-/

open PD PD.Tau PD.BaseTheorems

namespace PD.Theorems.Tau

/-- Shared shorthand for the two masses. -/
private abbrev coopMass (w : Tmpl → Nat) : Nat := w .coop + (w .tftSim + (w .tftPf + w .dupoc))
private abbrev eMass (w : Tmpl → Nat) : Nat := w .tftSim + (w .tftPf + w .dupoc)

/-! ## Constants -/

theorem outcome_TauCooperate_vs_TauDefect (k : Nat) (w : Tmpl → Nat) (θ : Nat)
    (hθ : θ ≤ w .coop + (w .defect + (w .tftSim + (w .tftPf + (w .dupoc + (w .ebot + 0))))))
    (hθ0 : θ ≠ 0) :
    ∃ N, outcome N (TauBotZ k .coop w θ) (TauBotZ k .defect w θ) = some (.C, .D) :=
  outcome_of_ex_plays
    ((tauCooperate_phase k w θ _).1 hθ)
    ((tauDefect_phase k w θ _).2 hθ0)

theorem outcome_TauDefect_vs_TauCooperate (k : Nat) (w : Tmpl → Nat) (θ : Nat)
    (hθ : θ ≤ w .coop + (w .defect + (w .tftSim + (w .tftPf + (w .dupoc + (w .ebot + 0))))))
    (hθ0 : θ ≠ 0) :
    ∃ N, outcome N (TauBotZ k .defect w θ) (TauBotZ k .coop w θ) = some (.D, .C) :=
  outcome_of_ex_plays
    ((tauDefect_phase k w θ _).2 hθ0)
    ((tauCooperate_phase k w θ _).1 hθ)

theorem outcome_TauCooperate_vs_TauCooperate (k : Nat) (w : Tmpl → Nat) (θ : Nat)
    (hθ : θ ≤ w .coop + (w .defect + (w .tftSim + (w .tftPf + (w .dupoc + (w .ebot + 0)))))) :
    ∃ N, outcome N (TauBotZ k .coop w θ) (TauBotZ k .coop w θ) = some (.C, .C) :=
  outcome_of_ex_plays
    ((tauCooperate_phase k w θ _).1 hθ)
    ((tauCooperate_phase k w θ _).1 hθ)

theorem outcome_TauDefect_vs_TauDefect (k : Nat) (w : Tmpl → Nat) (θ : Nat)
    (hθ0 : θ ≠ 0) :
    ∃ N, outcome N (TauBotZ k .defect w θ) (TauBotZ k .defect w θ) = some (.D, .D) :=
  outcome_of_ex_plays
    ((tauDefect_phase k w θ _).2 hθ0)
    ((tauDefect_phase k w θ _).2 hθ0)

/-! ## The cooperative regime (`θ ≤ coopMass`) — incl. the `(C, D)` exploitation
cells against TauDefect: a tau player acts on its SIGNAL, and a wrong signal costs
payoff. -/

theorem outcome_TauTFTPf_vs_TauTFTPf {k : Nat} (hk : 2 ≤ k) (hkk : c_guard k + 3 ≤ k)
    (h6 : 6 ≤ k) (θ : Nat) (w : Tmpl → Nat) (hθ : θ ≤ coopMass w) :
    ∃ N, outcome N (TauBotZ k .tftPf w θ) (TauBotZ k .tftPf w θ) = some (.C, .C) :=
  outcome_of_ex_plays
    ((tauTFTPf_phase hk hkk h6 θ w _).1 hθ)
    ((tauTFTPf_phase hk hkk h6 θ w _).1 hθ)

theorem outcome_TauTFTSim_vs_TauTFTSim {k : Nat} (hk : 2 ≤ k) (hkk : c_guard k + 3 ≤ k)
    (h6 : 6 ≤ k) (θ : Nat) (w : Tmpl → Nat) (hθ : θ ≤ coopMass w) :
    ∃ N, outcome N (TauBotZ k .tftSim w θ) (TauBotZ k .tftSim w θ) = some (.C, .C) :=
  outcome_of_ex_plays
    ((tauTFTSim_phase hk hkk h6 θ w _).1 hθ)
    ((tauTFTSim_phase hk hkk h6 θ w _).1 hθ)

theorem outcome_TauTFTPf_vs_TauTFTSim {k : Nat} (hk : 2 ≤ k) (hkk : c_guard k + 3 ≤ k)
    (h6 : 6 ≤ k) (θ : Nat) (w : Tmpl → Nat) (hθ : θ ≤ coopMass w) :
    ∃ N, outcome N (TauBotZ k .tftPf w θ) (TauBotZ k .tftSim w θ) = some (.C, .C) :=
  outcome_of_ex_plays
    ((tauTFTPf_phase hk hkk h6 θ w _).1 hθ)
    ((tauTFTSim_phase hk hkk h6 θ w _).1 hθ)

theorem outcome_TauTFTSim_vs_TauTFTPf {k : Nat} (hk : 2 ≤ k) (hkk : c_guard k + 3 ≤ k)
    (h6 : 6 ≤ k) (θ : Nat) (w : Tmpl → Nat) (hθ : θ ≤ coopMass w) :
    ∃ N, outcome N (TauBotZ k .tftSim w θ) (TauBotZ k .tftPf w θ) = some (.C, .C) :=
  outcome_of_ex_plays
    ((tauTFTSim_phase hk hkk h6 θ w _).1 hθ)
    ((tauTFTPf_phase hk hkk h6 θ w _).1 hθ)

/-! ## τ(DupocBot) — the Löb-gated cells -/

theorem outcome_TauDupoc_vs_TauDupoc :
    ∃ k₂, ∀ k, k₂ < k → ∀ θ (w : Tmpl → Nat), θ ≤ coopMass w →
      ∃ N, outcome N (TauBotZ k .dupoc w θ) (TauBotZ k .dupoc w θ) = some (.C, .C) := by
  obtain ⟨k₂, h⟩ := tauDupoc_phase
  exact ⟨k₂, fun k hk θ w hθ =>
    outcome_of_ex_plays ((h k hk θ w _).1 hθ) ((h k hk θ w _).1 hθ)⟩

theorem outcome_TauDupoc_vs_TauTFTPf :
    ∃ k₂, ∀ k, k₂ < k → 2 ≤ k → c_guard k + 3 ≤ k → 6 ≤ k →
      ∀ θ (w : Tmpl → Nat), θ ≤ coopMass w →
      ∃ N, outcome N (TauBotZ k .dupoc w θ) (TauBotZ k .tftPf w θ) = some (.C, .C) := by
  obtain ⟨k₂, h⟩ := tauDupoc_phase
  exact ⟨k₂, fun k hk hk2 hkk h6 θ w hθ =>
    outcome_of_ex_plays ((h k hk θ w _).1 hθ)
      ((tauTFTPf_phase hk2 hkk h6 θ w _).1 hθ)⟩

/-! ## τ(EBot) — the ONE-SIDED boundary (`θ ≤ eMass`, no window) -/

theorem outcome_TauEBot_vs_TauEBot_coop {k : Nat} (hk : 2 ≤ k) (hkk : c_guard k + 3 ≤ k)
    (h6 : 6 ≤ k) (θ : Nat) (w : Tmpl → Nat) (hθ : θ ≤ eMass w) :
    ∃ N, outcome N (TauBotZ k .ebot w θ) (TauBotZ k .ebot w θ) = some (.C, .C) :=
  outcome_of_ex_plays
    ((tauEBot_phase hk hkk h6 θ w _).1 hθ)
    ((tauEBot_phase hk hkk h6 θ w _).1 hθ)

theorem outcome_TauEBot_vs_TauEBot_high {k : Nat} (hk : 2 ≤ k) (hkk : c_guard k + 3 ≤ k)
    (h6 : 6 ≤ k) (θ : Nat) (w : Tmpl → Nat) (hθ : ¬ θ ≤ eMass w) :
    ∃ N, outcome N (TauBotZ k .ebot w θ) (TauBotZ k .ebot w θ) = some (.D, .D) :=
  outcome_of_ex_plays
    ((tauEBot_phase hk hkk h6 θ w _).2 hθ)
    ((tauEBot_phase hk hkk h6 θ w _).2 hθ)

/-- **THE SEPARATING BAND** `eMass < θ ≤ coopMass` (nonempty iff `w .coop > 0`):
    cooperators still cooperate while τ(EBot) has already flipped — the one-sided
    boundary made observable as a matrix cell. -/
theorem outcome_TauTFTPf_vs_TauEBot_band {k : Nat} (hk : 2 ≤ k) (hkk : c_guard k + 3 ≤ k)
    (h6 : 6 ≤ k) (θ : Nat) (w : Tmpl → Nat)
    (hlo : ¬ θ ≤ eMass w) (hhi : θ ≤ coopMass w) :
    ∃ N, outcome N (TauBotZ k .tftPf w θ) (TauBotZ k .ebot w θ) = some (.C, .D) :=
  outcome_of_ex_plays
    ((tauTFTPf_phase hk hkk h6 θ w _).1 hhi)
    ((tauEBot_phase hk hkk h6 θ w _).2 hlo)

theorem outcome_TauEBot_vs_TauTFTPf_band {k : Nat} (hk : 2 ≤ k) (hkk : c_guard k + 3 ≤ k)
    (h6 : 6 ≤ k) (θ : Nat) (w : Tmpl → Nat)
    (hlo : ¬ θ ≤ eMass w) (hhi : θ ≤ coopMass w) :
    ∃ N, outcome N (TauBotZ k .ebot w θ) (TauBotZ k .tftPf w θ) = some (.D, .C) :=
  outcome_of_ex_plays
    ((tauEBot_phase hk hkk h6 θ w _).2 hlo)
    ((tauTFTPf_phase hk hkk h6 θ w _).1 hhi)

/-- Inside the shared cooperative regime the exploiter reciprocates the prover TFT. -/
theorem outcome_TauEBot_vs_TauTFTPf_coop {k : Nat} (hk : 2 ≤ k) (hkk : c_guard k + 3 ≤ k)
    (h6 : 6 ≤ k) (θ : Nat) (w : Tmpl → Nat) (hθ : θ ≤ eMass w) :
    ∃ N, outcome N (TauBotZ k .ebot w θ) (TauBotZ k .tftPf w θ) = some (.C, .C) :=
  outcome_of_ex_plays
    ((tauEBot_phase hk hkk h6 θ w _).1 hθ)
    ((tauTFTPf_phase hk hkk h6 θ w _).1 (by simp only [coopMass, eMass] at *; omega))

end PD.Theorems.Tau
