import PrisonersDilemma.Tau.VotePhases

/-!
# Theorems/Tau/VoteMatrix — the refined Def-4 outcome matrix (2026-08-18)

Ordered outcomes of the six-template tau zoo under the corrected definition (the
uniform source lift τ; `Research/Notes/DEF4_TVOTE_ROADMAP.md`). Every cell is a
corollary of the α-phase theorems: tau players are `.opp`-free, hence extensionally
constant, so the matrix is the product of the play vector with itself.

**Two α-regimes, and they differ per bot.** The three cooperators share the boundary
`θ ≤ wC + wTs + wTp + wL`; τ(EBot)'s is `θ ≤ wTs + wTp + wL` — strictly lower, and
ONE-SIDED (no window). Cells are therefore stated per regime, with the hypotheses each
theorem actually needs.

This file REPLACES `Theorems/Tau/Matrix.lean`, whose 79 theorems were about the
retracted σ-players (33 of them about the "crowd-exploiter" that is not a lift of
EBot).
-/

open PD PD.Tau PD.BaseTheorems

namespace PD.Theorems.Tau

open PD.Tau (TauCooperate TauDefect TauDupoc TauTFTPf TauTFTSim TauEBot)

/-! ## Constants -/

theorem outcome_TauCooperate_vs_TauDefect (wC wD wTs wTp wL wE θ : Nat)
    (hθ : θ ≤ wC + (wD + (wTs + (wTp + (wL + (wE + 0)))))) (hθ0 : θ ≠ 0) :
    ∃ N, outcome N (TauCooperate wC wD wTs wTp wL wE θ)
      (TauDefect wC wD wTs wTp wL wE θ) = some (.C, .D) :=
  outcome_of_ex_plays
    ((tauCooperate_phase wC wD wTs wTp wL wE θ _).1 hθ)
    ((tauDefect_phase wC wD wTs wTp wL wE θ _).2 hθ0)

theorem outcome_TauDefect_vs_TauCooperate (wC wD wTs wTp wL wE θ : Nat)
    (hθ : θ ≤ wC + (wD + (wTs + (wTp + (wL + (wE + 0)))))) (hθ0 : θ ≠ 0) :
    ∃ N, outcome N (TauDefect wC wD wTs wTp wL wE θ)
      (TauCooperate wC wD wTs wTp wL wE θ) = some (.D, .C) :=
  outcome_of_ex_plays
    ((tauDefect_phase wC wD wTs wTp wL wE θ _).2 hθ0)
    ((tauCooperate_phase wC wD wTs wTp wL wE θ _).1 hθ)

theorem outcome_TauCooperate_vs_TauCooperate (wC wD wTs wTp wL wE θ : Nat)
    (hθ : θ ≤ wC + (wD + (wTs + (wTp + (wL + (wE + 0)))))) :
    ∃ N, outcome N (TauCooperate wC wD wTs wTp wL wE θ)
      (TauCooperate wC wD wTs wTp wL wE θ) = some (.C, .C) :=
  outcome_of_ex_plays
    ((tauCooperate_phase wC wD wTs wTp wL wE θ _).1 hθ)
    ((tauCooperate_phase wC wD wTs wTp wL wE θ _).1 hθ)

theorem outcome_TauDefect_vs_TauDefect (wC wD wTs wTp wL wE θ : Nat) (hθ0 : θ ≠ 0) :
    ∃ N, outcome N (TauDefect wC wD wTs wTp wL wE θ)
      (TauDefect wC wD wTs wTp wL wE θ) = some (.D, .D) :=
  outcome_of_ex_plays
    ((tauDefect_phase wC wD wTs wTp wL wE θ _).2 hθ0)
    ((tauDefect_phase wC wD wTs wTp wL wE θ _).2 hθ0)

/-! ## The cooperative regime (`θ ≤ wC + wTs + wTp + wL`)

Where all three cooperators cooperate. Note they cooperate against EVERY opponent —
including TauDefect, which is the `(C, D)` exploitation cell: acting on a signal means
a wrong signal costs payoff, the price of partial transparency. -/

theorem outcome_TauTFTPf_vs_TauTFTPf {k : Nat} (hk : 2 ≤ k) (hkk : c_guard k + 3 ≤ k)
    (h6 : 6 ≤ k) (θ wC wD wTs wTp wL wE : Nat) (hθ : θ ≤ wC + (wTs + (wTp + wL))) :
    ∃ N, outcome N (TauTFTPf k θ wC wD wTs wTp wL wE)
      (TauTFTPf k θ wC wD wTs wTp wL wE) = some (.C, .C) :=
  outcome_of_ex_plays
    ((tauTFTPf_phase hk hkk h6 θ wC wD wTs wTp wL wE _).1 hθ)
    ((tauTFTPf_phase hk hkk h6 θ wC wD wTs wTp wL wE _).1 hθ)

theorem outcome_TauTFTSim_vs_TauTFTSim {k : Nat} (hk : 2 ≤ k) (hkk : c_guard k + 3 ≤ k)
    (h6 : 6 ≤ k) (θ wC wD wTs wTp wL wE : Nat) (hθ : θ ≤ wC + (wTs + (wTp + wL))) :
    ∃ N, outcome N (TauTFTSim k θ wC wD wTs wTp wL wE)
      (TauTFTSim k θ wC wD wTs wTp wL wE) = some (.C, .C) :=
  outcome_of_ex_plays
    ((tauTFTSim_phase hk hkk h6 θ wC wD wTs wTp wL wE _).1 hθ)
    ((tauTFTSim_phase hk hkk h6 θ wC wD wTs wTp wL wE _).1 hθ)

theorem outcome_TauTFTPf_vs_TauTFTSim {k : Nat} (hk : 2 ≤ k) (hkk : c_guard k + 3 ≤ k)
    (h6 : 6 ≤ k) (θ wC wD wTs wTp wL wE : Nat) (hθ : θ ≤ wC + (wTs + (wTp + wL))) :
    ∃ N, outcome N (TauTFTPf k θ wC wD wTs wTp wL wE)
      (TauTFTSim k θ wC wD wTs wTp wL wE) = some (.C, .C) :=
  outcome_of_ex_plays
    ((tauTFTPf_phase hk hkk h6 θ wC wD wTs wTp wL wE _).1 hθ)
    ((tauTFTSim_phase hk hkk h6 θ wC wD wTs wTp wL wE _).1 hθ)

theorem outcome_TauTFTSim_vs_TauTFTPf {k : Nat} (hk : 2 ≤ k) (hkk : c_guard k + 3 ≤ k)
    (h6 : 6 ≤ k) (θ wC wD wTs wTp wL wE : Nat) (hθ : θ ≤ wC + (wTs + (wTp + wL))) :
    ∃ N, outcome N (TauTFTSim k θ wC wD wTs wTp wL wE)
      (TauTFTPf k θ wC wD wTs wTp wL wE) = some (.C, .C) :=
  outcome_of_ex_plays
    ((tauTFTSim_phase hk hkk h6 θ wC wD wTs wTp wL wE _).1 hθ)
    ((tauTFTPf_phase hk hkk h6 θ wC wD wTs wTp wL wE _).1 hθ)

/-! ## τ(DupocBot) — the Löb-gated cells -/

theorem outcome_TauDupoc_vs_TauDupoc :
    ∃ k₂, ∀ k, k₂ < k → ∀ θ wC wD wTs wTp wL wE, θ ≤ wC + (wTs + (wTp + wL)) →
      ∃ N, outcome N (TauDupoc k θ wC wD wTs wTp wL wE)
        (TauDupoc k θ wC wD wTs wTp wL wE) = some (.C, .C) := by
  obtain ⟨k₂, h⟩ := tauDupoc_phase
  exact ⟨k₂, fun k hk θ wC wD wTs wTp wL wE hθ =>
    outcome_of_ex_plays ((h k hk θ wC wD wTs wTp wL wE _).1 hθ)
      ((h k hk θ wC wD wTs wTp wL wE _).1 hθ)⟩

theorem outcome_TauDupoc_vs_TauTFTPf :
    ∃ k₂, ∀ k, k₂ < k → 2 ≤ k → c_guard k + 3 ≤ k → 6 ≤ k →
      ∀ θ wC wD wTs wTp wL wE, θ ≤ wC + (wTs + (wTp + wL)) →
      ∃ N, outcome N (TauDupoc k θ wC wD wTs wTp wL wE)
        (TauTFTPf k θ wC wD wTs wTp wL wE) = some (.C, .C) := by
  obtain ⟨k₂, h⟩ := tauDupoc_phase
  exact ⟨k₂, fun k hk hk2 hkk h6 θ wC wD wTs wTp wL wE hθ =>
    outcome_of_ex_plays ((h k hk θ wC wD wTs wTp wL wE _).1 hθ)
      ((tauTFTPf_phase hk2 hkk h6 θ wC wD wTs wTp wL wE _).1 hθ)⟩

/-! ## τ(EBot) — the ONE-SIDED boundary

`θ ≤ wTs + wTp + wL` (strictly below the cooperators' boundary, since it excludes
`wC`: EBot EXPLOITS the cooperator rather than reciprocating it). No window: above the
boundary it simply defects.

The retracted crowd-exploiter's window cells (`_exploitθ`/`_window`/`_highθ`, 33 of
them) have no counterpart here — that shape was an artifact of thresholding each
cascade STAGE. -/

theorem outcome_TauEBot_vs_TauEBot_coop {k : Nat} (hk : 2 ≤ k) (hkk : c_guard k + 3 ≤ k)
    (h6 : 6 ≤ k) (θ wC wD wTs wTp wL wE : Nat) (hθ : θ ≤ wTs + (wTp + wL)) :
    ∃ N, outcome N (TauEBot k θ wC wD wTs wTp wL wE)
      (TauEBot k θ wC wD wTs wTp wL wE) = some (.C, .C) :=
  outcome_of_ex_plays
    ((tauEBot_phase hk hkk h6 θ wC wD wTs wTp wL wE _).1 hθ)
    ((tauEBot_phase hk hkk h6 θ wC wD wTs wTp wL wE _).1 hθ)

theorem outcome_TauEBot_vs_TauEBot_high {k : Nat} (hk : 2 ≤ k) (hkk : c_guard k + 3 ≤ k)
    (h6 : 6 ≤ k) (θ wC wD wTs wTp wL wE : Nat) (hθ : ¬ θ ≤ wTs + (wTp + wL)) :
    ∃ N, outcome N (TauEBot k θ wC wD wTs wTp wL wE)
      (TauEBot k θ wC wD wTs wTp wL wE) = some (.D, .D) :=
  outcome_of_ex_plays
    ((tauEBot_phase hk hkk h6 θ wC wD wTs wTp wL wE _).2 hθ)
    ((tauEBot_phase hk hkk h6 θ wC wD wTs wTp wL wE _).2 hθ)

/-- **THE SEPARATING CELL of the corrected definition.** In the band
    `wTs + wTp + wL < θ ≤ wC + wTs + wTp + wL` — nonempty exactly when `wC > 0` — the
    cooperators still cooperate while τ(EBot) has already flipped to defection, because
    its mass excludes the cooperator weight it exploits. This band is where the
    exploiter's one-sided boundary is observable. -/
theorem outcome_TauTFTPf_vs_TauEBot_band {k : Nat} (hk : 2 ≤ k) (hkk : c_guard k + 3 ≤ k)
    (h6 : 6 ≤ k) (θ wC wD wTs wTp wL wE : Nat)
    (hlo : ¬ θ ≤ wTs + (wTp + wL)) (hhi : θ ≤ wC + (wTs + (wTp + wL))) :
    ∃ N, outcome N (TauTFTPf k θ wC wD wTs wTp wL wE)
      (TauEBot k θ wC wD wTs wTp wL wE) = some (.C, .D) :=
  outcome_of_ex_plays
    ((tauTFTPf_phase hk hkk h6 θ wC wD wTs wTp wL wE _).1 hhi)
    ((tauEBot_phase hk hkk h6 θ wC wD wTs wTp wL wE _).2 hlo)

theorem outcome_TauEBot_vs_TauTFTPf_band {k : Nat} (hk : 2 ≤ k) (hkk : c_guard k + 3 ≤ k)
    (h6 : 6 ≤ k) (θ wC wD wTs wTp wL wE : Nat)
    (hlo : ¬ θ ≤ wTs + (wTp + wL)) (hhi : θ ≤ wC + (wTs + (wTp + wL))) :
    ∃ N, outcome N (TauEBot k θ wC wD wTs wTp wL wE)
      (TauTFTPf k θ wC wD wTs wTp wL wE) = some (.D, .C) :=
  outcome_of_ex_plays
    ((tauEBot_phase hk hkk h6 θ wC wD wTs wTp wL wE _).2 hlo)
    ((tauTFTPf_phase hk hkk h6 θ wC wD wTs wTp wL wE _).1 hhi)

/-- Inside the shared cooperative regime, the exploiter reciprocates the prover TFT. -/
theorem outcome_TauEBot_vs_TauTFTPf_coop {k : Nat} (hk : 2 ≤ k) (hkk : c_guard k + 3 ≤ k)
    (h6 : 6 ≤ k) (θ wC wD wTs wTp wL wE : Nat) (hθ : θ ≤ wTs + (wTp + wL)) :
    ∃ N, outcome N (TauEBot k θ wC wD wTs wTp wL wE)
      (TauTFTPf k θ wC wD wTs wTp wL wE) = some (.C, .C) :=
  outcome_of_ex_plays
    ((tauEBot_phase hk hkk h6 θ wC wD wTs wTp wL wE _).1 hθ)
    ((tauTFTPf_phase hk hkk h6 θ wC wD wTs wTp wL wE _).1 (by omega))

end PD.Theorems.Tau
