import PrisonersDilemma.Tau.Phases

/-!
# Theorems/Tau/Matrix — the Def-4 outcome matrix (cascade zoo, 2026-08-12)

**⚠ RETRACTION (2026-08-13):** the σ-player reading of this matrix is OUTDATED —
correct Def 4 is the uniform source lift, under which Def 4 coincides with Def 3
(see `Tau/Defs.lean` banner + design note Part III). Every theorem here is
kernel-true about the IMPLEMENTED programs, but the 33 TauEBot cells (window /
exploitθ / highθ) describe the crowd-exploiter, NOT τ(EBot), and must not be
cited as Def-4 results pending the σ-player redefinition.

The ordered outcomes of the 6-template tau zoo, per α-regime — all corollaries of
the phase theorems (`Tau/Phases`): tau players are `.opp`-free, hence extensionally
constant, so the matrix is the product of the play vector with itself and each cell
is one `outcome_of_ex_plays`.

**Regimes.** The three cooperators (TauDupoc, TauTFTSim, TauTFTPf) share ONE
boundary, `θ ≤ wC + wTs + wTp + wL` — TauDupoc's mass now honestly EXCLUDES `wE`
(`E(δ_L)` cooperates but only floor-priced, so its bit is 0). TauEBot's cooperation
region is a WINDOW: it defects when its exploit stage fires (`θ ≤ wC`,
`_exploitθ` cells), cooperates inside `wC < θ ≤ wC + wTs + wTp + wL` (the
unsuffixed cells), and defects above (`_highθ`). Because the cooperators' masses
coincide, no mixed regime exists between them — the former `_mixedRC/_mixedCR`
Dupoc↔TFT cells were artifacts of the retired stipulated `E(δ_L)` bit and are gone.

Notable cells: the θ-bots cooperate even AGAINST TauDefect — `(C, D)` exploitation.
That is correct Def-4 semantics: a tau player acts on its SIGNAL, and a wrong signal
costs payoff. And in the exploit regime TauEBot defects against cooperators that
cooperate with it — the lifted exploiter exploits.

(Single-file layout, deviating from the per-pair convention: tau cells are not
base-matrix cells — no sheet sync — and the plays are opponent-independent.)
-/

open PD PD.Tau

namespace PD.Theorems.Tau

/-! ## Constant vs constant -/

theorem outcome_TauCooperate_vs_TauCooperate :
    ∃ N, outcome N TauCooperate TauCooperate = some (.C, .C) :=
  outcome_of_ex_plays (tauCooperate_plays _) (tauCooperate_plays _)

theorem outcome_TauCooperate_vs_TauDefect :
    ∃ N, outcome N TauCooperate TauDefect = some (.C, .D) :=
  outcome_of_ex_plays (tauCooperate_plays _) (tauDefect_plays _)

theorem outcome_TauDefect_vs_TauCooperate :
    ∃ N, outcome N TauDefect TauCooperate = some (.D, .C) :=
  outcome_of_ex_plays (tauDefect_plays _) (tauCooperate_plays _)

theorem outcome_TauDefect_vs_TauDefect :
    ∃ N, outcome N TauDefect TauDefect = some (.D, .D) :=
  outcome_of_ex_plays (tauDefect_plays _) (tauDefect_plays _)

/-! ## The cooperators vs the constants -/

theorem outcome_TauDupoc_vs_TauCooperate :
    ∃ k₂, ∀ k, k₂ < k → ∀ θ wC wD wTs wTp wL wE, θ ≤ wC + wTs + wTp + wL →
      ∃ N, outcome N (TauDupoc k θ wC wD wTs wTp wL wE) TauCooperate
        = some (.C, .C) := by
  obtain ⟨k₂, h⟩ := tauDupoc_phase
  refine ⟨k₂, fun k hk θ wC wD wTs wTp wL wE hθ => ?_⟩
  exact outcome_of_ex_plays ((h k hk θ wC wD wTs wTp wL wE _).1 hθ) (tauCooperate_plays _)

theorem outcome_TauCooperate_vs_TauDupoc :
    ∃ k₂, ∀ k, k₂ < k → ∀ θ wC wD wTs wTp wL wE, θ ≤ wC + wTs + wTp + wL →
      ∃ N, outcome N TauCooperate (TauDupoc k θ wC wD wTs wTp wL wE)
        = some (.C, .C) := by
  obtain ⟨k₂, h⟩ := tauDupoc_phase
  refine ⟨k₂, fun k hk θ wC wD wTs wTp wL wE hθ => ?_⟩
  exact outcome_of_ex_plays (tauCooperate_plays _) ((h k hk θ wC wD wTs wTp wL wE _).1 hθ)

theorem outcome_TauDupoc_vs_TauDefect :
    ∃ k₂, ∀ k, k₂ < k → ∀ θ wC wD wTs wTp wL wE, θ ≤ wC + wTs + wTp + wL →
      ∃ N, outcome N (TauDupoc k θ wC wD wTs wTp wL wE) TauDefect
        = some (.C, .D) := by
  obtain ⟨k₂, h⟩ := tauDupoc_phase
  refine ⟨k₂, fun k hk θ wC wD wTs wTp wL wE hθ => ?_⟩
  exact outcome_of_ex_plays ((h k hk θ wC wD wTs wTp wL wE _).1 hθ) (tauDefect_plays _)

theorem outcome_TauDefect_vs_TauDupoc :
    ∃ k₂, ∀ k, k₂ < k → ∀ θ wC wD wTs wTp wL wE, θ ≤ wC + wTs + wTp + wL →
      ∃ N, outcome N TauDefect (TauDupoc k θ wC wD wTs wTp wL wE)
        = some (.D, .C) := by
  obtain ⟨k₂, h⟩ := tauDupoc_phase
  refine ⟨k₂, fun k hk θ wC wD wTs wTp wL wE hθ => ?_⟩
  exact outcome_of_ex_plays (tauDefect_plays _) ((h k hk θ wC wD wTs wTp wL wE _).1 hθ)

theorem outcome_TauTFTSim_vs_TauCooperate :
    ∃ k₂, ∀ k, k₂ < k → ∀ θ wC wD wTs wTp wL wE, θ ≤ wC + wTs + wTp + wL →
      ∃ N, outcome N (TauTFTSim k θ wC wD wTs wTp wL wE) TauCooperate
        = some (.C, .C) := by
  obtain ⟨k₂, h⟩ := tauTFTSim_phase
  refine ⟨k₂, fun k hk θ wC wD wTs wTp wL wE hθ => ?_⟩
  exact outcome_of_ex_plays ((h k hk θ wC wD wTs wTp wL wE _).1 hθ) (tauCooperate_plays _)

theorem outcome_TauCooperate_vs_TauTFTSim :
    ∃ k₂, ∀ k, k₂ < k → ∀ θ wC wD wTs wTp wL wE, θ ≤ wC + wTs + wTp + wL →
      ∃ N, outcome N TauCooperate (TauTFTSim k θ wC wD wTs wTp wL wE)
        = some (.C, .C) := by
  obtain ⟨k₂, h⟩ := tauTFTSim_phase
  refine ⟨k₂, fun k hk θ wC wD wTs wTp wL wE hθ => ?_⟩
  exact outcome_of_ex_plays (tauCooperate_plays _) ((h k hk θ wC wD wTs wTp wL wE _).1 hθ)

theorem outcome_TauTFTSim_vs_TauDefect :
    ∃ k₂, ∀ k, k₂ < k → ∀ θ wC wD wTs wTp wL wE, θ ≤ wC + wTs + wTp + wL →
      ∃ N, outcome N (TauTFTSim k θ wC wD wTs wTp wL wE) TauDefect
        = some (.C, .D) := by
  obtain ⟨k₂, h⟩ := tauTFTSim_phase
  refine ⟨k₂, fun k hk θ wC wD wTs wTp wL wE hθ => ?_⟩
  exact outcome_of_ex_plays ((h k hk θ wC wD wTs wTp wL wE _).1 hθ) (tauDefect_plays _)

theorem outcome_TauDefect_vs_TauTFTSim :
    ∃ k₂, ∀ k, k₂ < k → ∀ θ wC wD wTs wTp wL wE, θ ≤ wC + wTs + wTp + wL →
      ∃ N, outcome N TauDefect (TauTFTSim k θ wC wD wTs wTp wL wE)
        = some (.D, .C) := by
  obtain ⟨k₂, h⟩ := tauTFTSim_phase
  refine ⟨k₂, fun k hk θ wC wD wTs wTp wL wE hθ => ?_⟩
  exact outcome_of_ex_plays (tauDefect_plays _) ((h k hk θ wC wD wTs wTp wL wE _).1 hθ)

theorem outcome_TauTFTPf_vs_TauCooperate :
    ∃ k₂, ∀ k, k₂ < k → ∀ θ wC wD wTs wTp wL wE, θ ≤ wC + wTs + wTp + wL →
      ∃ N, outcome N (TauTFTPf k θ wC wD wTs wTp wL wE) TauCooperate
        = some (.C, .C) := by
  obtain ⟨k₂, h⟩ := tauTFTPf_phase
  refine ⟨k₂, fun k hk θ wC wD wTs wTp wL wE hθ => ?_⟩
  exact outcome_of_ex_plays ((h k hk θ wC wD wTs wTp wL wE _).1 hθ) (tauCooperate_plays _)

theorem outcome_TauCooperate_vs_TauTFTPf :
    ∃ k₂, ∀ k, k₂ < k → ∀ θ wC wD wTs wTp wL wE, θ ≤ wC + wTs + wTp + wL →
      ∃ N, outcome N TauCooperate (TauTFTPf k θ wC wD wTs wTp wL wE)
        = some (.C, .C) := by
  obtain ⟨k₂, h⟩ := tauTFTPf_phase
  refine ⟨k₂, fun k hk θ wC wD wTs wTp wL wE hθ => ?_⟩
  exact outcome_of_ex_plays (tauCooperate_plays _) ((h k hk θ wC wD wTs wTp wL wE _).1 hθ)

theorem outcome_TauTFTPf_vs_TauDefect :
    ∃ k₂, ∀ k, k₂ < k → ∀ θ wC wD wTs wTp wL wE, θ ≤ wC + wTs + wTp + wL →
      ∃ N, outcome N (TauTFTPf k θ wC wD wTs wTp wL wE) TauDefect
        = some (.C, .D) := by
  obtain ⟨k₂, h⟩ := tauTFTPf_phase
  refine ⟨k₂, fun k hk θ wC wD wTs wTp wL wE hθ => ?_⟩
  exact outcome_of_ex_plays ((h k hk θ wC wD wTs wTp wL wE _).1 hθ) (tauDefect_plays _)

theorem outcome_TauDefect_vs_TauTFTPf :
    ∃ k₂, ∀ k, k₂ < k → ∀ θ wC wD wTs wTp wL wE, θ ≤ wC + wTs + wTp + wL →
      ∃ N, outcome N TauDefect (TauTFTPf k θ wC wD wTs wTp wL wE)
        = some (.D, .C) := by
  obtain ⟨k₂, h⟩ := tauTFTPf_phase
  refine ⟨k₂, fun k hk θ wC wD wTs wTp wL wE hθ => ?_⟩
  exact outcome_of_ex_plays (tauDefect_plays _) ((h k hk θ wC wD wTs wTp wL wE _).1 hθ)

/-! ## Cooperator pairs (one shared boundary — no mixed regime exists) -/

/-- **Löbian self-cooperation, Def-4 edition**: TauDupoc vs itself is `(C, C)` in the
    cooperative regime — via the quine fixpoint bit, not via reading the opponent. -/
theorem outcome_TauDupoc_vs_TauDupoc :
    ∃ k₂, ∀ k, k₂ < k → ∀ θ wC wD wTs wTp wL wE, θ ≤ wC + wTs + wTp + wL →
      ∃ N, outcome N (TauDupoc k θ wC wD wTs wTp wL wE) (TauDupoc k θ wC wD wTs wTp wL wE)
        = some (.C, .C) := by
  obtain ⟨k₂, h⟩ := tauDupoc_phase
  refine ⟨k₂, fun k hk θ wC wD wTs wTp wL wE hθ => ?_⟩
  exact outcome_of_ex_plays
    ((h k hk θ wC wD wTs wTp wL wE _).1 hθ)
    ((h k hk θ wC wD wTs wTp wL wE _).1 hθ)

theorem outcome_TauDupoc_vs_TauTFTSim :
    ∃ k₂, ∀ k, k₂ < k → ∀ θ wC wD wTs wTp wL wE, θ ≤ wC + wTs + wTp + wL →
      ∃ N, outcome N (TauDupoc k θ wC wD wTs wTp wL wE) (TauTFTSim k θ wC wD wTs wTp wL wE)
        = some (.C, .C) := by
  obtain ⟨k₁, h₁⟩ := tauDupoc_phase
  obtain ⟨k₂, h₂⟩ := tauTFTSim_phase
  refine ⟨max k₁ k₂, fun k hk θ wC wD wTs wTp wL wE hθ => ?_⟩
  exact outcome_of_ex_plays
    ((h₁ k (lt_of_le_of_lt (Nat.le_max_left _ _) hk) θ wC wD wTs wTp wL wE _).1 hθ)
    ((h₂ k (lt_of_le_of_lt (Nat.le_max_right _ _) hk) θ wC wD wTs wTp wL wE _).1 hθ)

theorem outcome_TauDupoc_vs_TauTFTPf :
    ∃ k₂, ∀ k, k₂ < k → ∀ θ wC wD wTs wTp wL wE, θ ≤ wC + wTs + wTp + wL →
      ∃ N, outcome N (TauDupoc k θ wC wD wTs wTp wL wE) (TauTFTPf k θ wC wD wTs wTp wL wE)
        = some (.C, .C) := by
  obtain ⟨k₁, h₁⟩ := tauDupoc_phase
  obtain ⟨k₂, h₂⟩ := tauTFTPf_phase
  refine ⟨max k₁ k₂, fun k hk θ wC wD wTs wTp wL wE hθ => ?_⟩
  exact outcome_of_ex_plays
    ((h₁ k (lt_of_le_of_lt (Nat.le_max_left _ _) hk) θ wC wD wTs wTp wL wE _).1 hθ)
    ((h₂ k (lt_of_le_of_lt (Nat.le_max_right _ _) hk) θ wC wD wTs wTp wL wE _).1 hθ)

theorem outcome_TauTFTSim_vs_TauDupoc :
    ∃ k₂, ∀ k, k₂ < k → ∀ θ wC wD wTs wTp wL wE, θ ≤ wC + wTs + wTp + wL →
      ∃ N, outcome N (TauTFTSim k θ wC wD wTs wTp wL wE) (TauDupoc k θ wC wD wTs wTp wL wE)
        = some (.C, .C) := by
  obtain ⟨k₁, h₁⟩ := tauTFTSim_phase
  obtain ⟨k₂, h₂⟩ := tauDupoc_phase
  refine ⟨max k₁ k₂, fun k hk θ wC wD wTs wTp wL wE hθ => ?_⟩
  exact outcome_of_ex_plays
    ((h₁ k (lt_of_le_of_lt (Nat.le_max_left _ _) hk) θ wC wD wTs wTp wL wE _).1 hθ)
    ((h₂ k (lt_of_le_of_lt (Nat.le_max_right _ _) hk) θ wC wD wTs wTp wL wE _).1 hθ)

theorem outcome_TauTFTSim_vs_TauTFTSim :
    ∃ k₂, ∀ k, k₂ < k → ∀ θ wC wD wTs wTp wL wE, θ ≤ wC + wTs + wTp + wL →
      ∃ N, outcome N (TauTFTSim k θ wC wD wTs wTp wL wE) (TauTFTSim k θ wC wD wTs wTp wL wE)
        = some (.C, .C) := by
  obtain ⟨k₂, h⟩ := tauTFTSim_phase
  refine ⟨k₂, fun k hk θ wC wD wTs wTp wL wE hθ => ?_⟩
  exact outcome_of_ex_plays
    ((h k hk θ wC wD wTs wTp wL wE _).1 hθ)
    ((h k hk θ wC wD wTs wTp wL wE _).1 hθ)

theorem outcome_TauTFTSim_vs_TauTFTPf :
    ∃ k₂, ∀ k, k₂ < k → ∀ θ wC wD wTs wTp wL wE, θ ≤ wC + wTs + wTp + wL →
      ∃ N, outcome N (TauTFTSim k θ wC wD wTs wTp wL wE) (TauTFTPf k θ wC wD wTs wTp wL wE)
        = some (.C, .C) := by
  obtain ⟨k₁, h₁⟩ := tauTFTSim_phase
  obtain ⟨k₂, h₂⟩ := tauTFTPf_phase
  refine ⟨max k₁ k₂, fun k hk θ wC wD wTs wTp wL wE hθ => ?_⟩
  exact outcome_of_ex_plays
    ((h₁ k (lt_of_le_of_lt (Nat.le_max_left _ _) hk) θ wC wD wTs wTp wL wE _).1 hθ)
    ((h₂ k (lt_of_le_of_lt (Nat.le_max_right _ _) hk) θ wC wD wTs wTp wL wE _).1 hθ)

theorem outcome_TauTFTPf_vs_TauDupoc :
    ∃ k₂, ∀ k, k₂ < k → ∀ θ wC wD wTs wTp wL wE, θ ≤ wC + wTs + wTp + wL →
      ∃ N, outcome N (TauTFTPf k θ wC wD wTs wTp wL wE) (TauDupoc k θ wC wD wTs wTp wL wE)
        = some (.C, .C) := by
  obtain ⟨k₁, h₁⟩ := tauTFTPf_phase
  obtain ⟨k₂, h₂⟩ := tauDupoc_phase
  refine ⟨max k₁ k₂, fun k hk θ wC wD wTs wTp wL wE hθ => ?_⟩
  exact outcome_of_ex_plays
    ((h₁ k (lt_of_le_of_lt (Nat.le_max_left _ _) hk) θ wC wD wTs wTp wL wE _).1 hθ)
    ((h₂ k (lt_of_le_of_lt (Nat.le_max_right _ _) hk) θ wC wD wTs wTp wL wE _).1 hθ)

theorem outcome_TauTFTPf_vs_TauTFTSim :
    ∃ k₂, ∀ k, k₂ < k → ∀ θ wC wD wTs wTp wL wE, θ ≤ wC + wTs + wTp + wL →
      ∃ N, outcome N (TauTFTPf k θ wC wD wTs wTp wL wE) (TauTFTSim k θ wC wD wTs wTp wL wE)
        = some (.C, .C) := by
  obtain ⟨k₁, h₁⟩ := tauTFTPf_phase
  obtain ⟨k₂, h₂⟩ := tauTFTSim_phase
  refine ⟨max k₁ k₂, fun k hk θ wC wD wTs wTp wL wE hθ => ?_⟩
  exact outcome_of_ex_plays
    ((h₁ k (lt_of_le_of_lt (Nat.le_max_left _ _) hk) θ wC wD wTs wTp wL wE _).1 hθ)
    ((h₂ k (lt_of_le_of_lt (Nat.le_max_right _ _) hk) θ wC wD wTs wTp wL wE _).1 hθ)

theorem outcome_TauTFTPf_vs_TauTFTPf :
    ∃ k₂, ∀ k, k₂ < k → ∀ θ wC wD wTs wTp wL wE, θ ≤ wC + wTs + wTp + wL →
      ∃ N, outcome N (TauTFTPf k θ wC wD wTs wTp wL wE) (TauTFTPf k θ wC wD wTs wTp wL wE)
        = some (.C, .C) := by
  obtain ⟨k₂, h⟩ := tauTFTPf_phase
  refine ⟨k₂, fun k hk θ wC wD wTs wTp wL wE hθ => ?_⟩
  exact outcome_of_ex_plays
    ((h k hk θ wC wD wTs wTp wL wE _).1 hθ)
    ((h k hk θ wC wD wTs wTp wL wE _).1 hθ)

/-! ## The α-flip: the defect regime (`_highθ`) -/

theorem outcome_TauDupoc_vs_TauCooperate_highθ :
    ∃ k₂, ∀ k, k₂ < k → ∀ θ wC wD wTs wTp wL wE, wC + wTs + wTp + wL < θ →
      ∃ N, outcome N (TauDupoc k θ wC wD wTs wTp wL wE) TauCooperate
        = some (.D, .C) := by
  obtain ⟨k₂, h⟩ := tauDupoc_phase
  refine ⟨k₂, fun k hk θ wC wD wTs wTp wL wE hθ => ?_⟩
  exact outcome_of_ex_plays ((h k hk θ wC wD wTs wTp wL wE _).2 hθ) (tauCooperate_plays _)

theorem outcome_TauCooperate_vs_TauDupoc_highθ :
    ∃ k₂, ∀ k, k₂ < k → ∀ θ wC wD wTs wTp wL wE, wC + wTs + wTp + wL < θ →
      ∃ N, outcome N TauCooperate (TauDupoc k θ wC wD wTs wTp wL wE)
        = some (.C, .D) := by
  obtain ⟨k₂, h⟩ := tauDupoc_phase
  refine ⟨k₂, fun k hk θ wC wD wTs wTp wL wE hθ => ?_⟩
  exact outcome_of_ex_plays (tauCooperate_plays _) ((h k hk θ wC wD wTs wTp wL wE _).2 hθ)

theorem outcome_TauDupoc_vs_TauDefect_highθ :
    ∃ k₂, ∀ k, k₂ < k → ∀ θ wC wD wTs wTp wL wE, wC + wTs + wTp + wL < θ →
      ∃ N, outcome N (TauDupoc k θ wC wD wTs wTp wL wE) TauDefect
        = some (.D, .D) := by
  obtain ⟨k₂, h⟩ := tauDupoc_phase
  refine ⟨k₂, fun k hk θ wC wD wTs wTp wL wE hθ => ?_⟩
  exact outcome_of_ex_plays ((h k hk θ wC wD wTs wTp wL wE _).2 hθ) (tauDefect_plays _)

theorem outcome_TauDefect_vs_TauDupoc_highθ :
    ∃ k₂, ∀ k, k₂ < k → ∀ θ wC wD wTs wTp wL wE, wC + wTs + wTp + wL < θ →
      ∃ N, outcome N TauDefect (TauDupoc k θ wC wD wTs wTp wL wE)
        = some (.D, .D) := by
  obtain ⟨k₂, h⟩ := tauDupoc_phase
  refine ⟨k₂, fun k hk θ wC wD wTs wTp wL wE hθ => ?_⟩
  exact outcome_of_ex_plays (tauDefect_plays _) ((h k hk θ wC wD wTs wTp wL wE _).2 hθ)

theorem outcome_TauTFTSim_vs_TauCooperate_highθ :
    ∃ k₂, ∀ k, k₂ < k → ∀ θ wC wD wTs wTp wL wE, wC + wTs + wTp + wL < θ →
      ∃ N, outcome N (TauTFTSim k θ wC wD wTs wTp wL wE) TauCooperate
        = some (.D, .C) := by
  obtain ⟨k₂, h⟩ := tauTFTSim_phase
  refine ⟨k₂, fun k hk θ wC wD wTs wTp wL wE hθ => ?_⟩
  exact outcome_of_ex_plays ((h k hk θ wC wD wTs wTp wL wE _).2 hθ) (tauCooperate_plays _)

theorem outcome_TauCooperate_vs_TauTFTSim_highθ :
    ∃ k₂, ∀ k, k₂ < k → ∀ θ wC wD wTs wTp wL wE, wC + wTs + wTp + wL < θ →
      ∃ N, outcome N TauCooperate (TauTFTSim k θ wC wD wTs wTp wL wE)
        = some (.C, .D) := by
  obtain ⟨k₂, h⟩ := tauTFTSim_phase
  refine ⟨k₂, fun k hk θ wC wD wTs wTp wL wE hθ => ?_⟩
  exact outcome_of_ex_plays (tauCooperate_plays _) ((h k hk θ wC wD wTs wTp wL wE _).2 hθ)

theorem outcome_TauTFTSim_vs_TauDefect_highθ :
    ∃ k₂, ∀ k, k₂ < k → ∀ θ wC wD wTs wTp wL wE, wC + wTs + wTp + wL < θ →
      ∃ N, outcome N (TauTFTSim k θ wC wD wTs wTp wL wE) TauDefect
        = some (.D, .D) := by
  obtain ⟨k₂, h⟩ := tauTFTSim_phase
  refine ⟨k₂, fun k hk θ wC wD wTs wTp wL wE hθ => ?_⟩
  exact outcome_of_ex_plays ((h k hk θ wC wD wTs wTp wL wE _).2 hθ) (tauDefect_plays _)

theorem outcome_TauDefect_vs_TauTFTSim_highθ :
    ∃ k₂, ∀ k, k₂ < k → ∀ θ wC wD wTs wTp wL wE, wC + wTs + wTp + wL < θ →
      ∃ N, outcome N TauDefect (TauTFTSim k θ wC wD wTs wTp wL wE)
        = some (.D, .D) := by
  obtain ⟨k₂, h⟩ := tauTFTSim_phase
  refine ⟨k₂, fun k hk θ wC wD wTs wTp wL wE hθ => ?_⟩
  exact outcome_of_ex_plays (tauDefect_plays _) ((h k hk θ wC wD wTs wTp wL wE _).2 hθ)

theorem outcome_TauTFTPf_vs_TauCooperate_highθ :
    ∃ k₂, ∀ k, k₂ < k → ∀ θ wC wD wTs wTp wL wE, wC + wTs + wTp + wL < θ →
      ∃ N, outcome N (TauTFTPf k θ wC wD wTs wTp wL wE) TauCooperate
        = some (.D, .C) := by
  obtain ⟨k₂, h⟩ := tauTFTPf_phase
  refine ⟨k₂, fun k hk θ wC wD wTs wTp wL wE hθ => ?_⟩
  exact outcome_of_ex_plays ((h k hk θ wC wD wTs wTp wL wE _).2 hθ) (tauCooperate_plays _)

theorem outcome_TauCooperate_vs_TauTFTPf_highθ :
    ∃ k₂, ∀ k, k₂ < k → ∀ θ wC wD wTs wTp wL wE, wC + wTs + wTp + wL < θ →
      ∃ N, outcome N TauCooperate (TauTFTPf k θ wC wD wTs wTp wL wE)
        = some (.C, .D) := by
  obtain ⟨k₂, h⟩ := tauTFTPf_phase
  refine ⟨k₂, fun k hk θ wC wD wTs wTp wL wE hθ => ?_⟩
  exact outcome_of_ex_plays (tauCooperate_plays _) ((h k hk θ wC wD wTs wTp wL wE _).2 hθ)

theorem outcome_TauTFTPf_vs_TauDefect_highθ :
    ∃ k₂, ∀ k, k₂ < k → ∀ θ wC wD wTs wTp wL wE, wC + wTs + wTp + wL < θ →
      ∃ N, outcome N (TauTFTPf k θ wC wD wTs wTp wL wE) TauDefect
        = some (.D, .D) := by
  obtain ⟨k₂, h⟩ := tauTFTPf_phase
  refine ⟨k₂, fun k hk θ wC wD wTs wTp wL wE hθ => ?_⟩
  exact outcome_of_ex_plays ((h k hk θ wC wD wTs wTp wL wE _).2 hθ) (tauDefect_plays _)

theorem outcome_TauDefect_vs_TauTFTPf_highθ :
    ∃ k₂, ∀ k, k₂ < k → ∀ θ wC wD wTs wTp wL wE, wC + wTs + wTp + wL < θ →
      ∃ N, outcome N TauDefect (TauTFTPf k θ wC wD wTs wTp wL wE)
        = some (.D, .D) := by
  obtain ⟨k₂, h⟩ := tauTFTPf_phase
  refine ⟨k₂, fun k hk θ wC wD wTs wTp wL wE hθ => ?_⟩
  exact outcome_of_ex_plays (tauDefect_plays _) ((h k hk θ wC wD wTs wTp wL wE _).2 hθ)

theorem outcome_TauDupoc_vs_TauDupoc_highθ :
    ∃ k₂, ∀ k, k₂ < k → ∀ θ wC wD wTs wTp wL wE, wC + wTs + wTp + wL < θ →
      ∃ N, outcome N (TauDupoc k θ wC wD wTs wTp wL wE) (TauDupoc k θ wC wD wTs wTp wL wE)
        = some (.D, .D) := by
  obtain ⟨k₂, h⟩ := tauDupoc_phase
  refine ⟨k₂, fun k hk θ wC wD wTs wTp wL wE hθ => ?_⟩
  exact outcome_of_ex_plays
    ((h k hk θ wC wD wTs wTp wL wE _).2 hθ)
    ((h k hk θ wC wD wTs wTp wL wE _).2 hθ)

theorem outcome_TauDupoc_vs_TauTFTSim_highθ :
    ∃ k₂, ∀ k, k₂ < k → ∀ θ wC wD wTs wTp wL wE, wC + wTs + wTp + wL < θ →
      ∃ N, outcome N (TauDupoc k θ wC wD wTs wTp wL wE) (TauTFTSim k θ wC wD wTs wTp wL wE)
        = some (.D, .D) := by
  obtain ⟨k₁, h₁⟩ := tauDupoc_phase
  obtain ⟨k₂, h₂⟩ := tauTFTSim_phase
  refine ⟨max k₁ k₂, fun k hk θ wC wD wTs wTp wL wE hθ => ?_⟩
  exact outcome_of_ex_plays
    ((h₁ k (lt_of_le_of_lt (Nat.le_max_left _ _) hk) θ wC wD wTs wTp wL wE _).2 hθ)
    ((h₂ k (lt_of_le_of_lt (Nat.le_max_right _ _) hk) θ wC wD wTs wTp wL wE _).2 hθ)

theorem outcome_TauDupoc_vs_TauTFTPf_highθ :
    ∃ k₂, ∀ k, k₂ < k → ∀ θ wC wD wTs wTp wL wE, wC + wTs + wTp + wL < θ →
      ∃ N, outcome N (TauDupoc k θ wC wD wTs wTp wL wE) (TauTFTPf k θ wC wD wTs wTp wL wE)
        = some (.D, .D) := by
  obtain ⟨k₁, h₁⟩ := tauDupoc_phase
  obtain ⟨k₂, h₂⟩ := tauTFTPf_phase
  refine ⟨max k₁ k₂, fun k hk θ wC wD wTs wTp wL wE hθ => ?_⟩
  exact outcome_of_ex_plays
    ((h₁ k (lt_of_le_of_lt (Nat.le_max_left _ _) hk) θ wC wD wTs wTp wL wE _).2 hθ)
    ((h₂ k (lt_of_le_of_lt (Nat.le_max_right _ _) hk) θ wC wD wTs wTp wL wE _).2 hθ)

theorem outcome_TauTFTSim_vs_TauDupoc_highθ :
    ∃ k₂, ∀ k, k₂ < k → ∀ θ wC wD wTs wTp wL wE, wC + wTs + wTp + wL < θ →
      ∃ N, outcome N (TauTFTSim k θ wC wD wTs wTp wL wE) (TauDupoc k θ wC wD wTs wTp wL wE)
        = some (.D, .D) := by
  obtain ⟨k₁, h₁⟩ := tauTFTSim_phase
  obtain ⟨k₂, h₂⟩ := tauDupoc_phase
  refine ⟨max k₁ k₂, fun k hk θ wC wD wTs wTp wL wE hθ => ?_⟩
  exact outcome_of_ex_plays
    ((h₁ k (lt_of_le_of_lt (Nat.le_max_left _ _) hk) θ wC wD wTs wTp wL wE _).2 hθ)
    ((h₂ k (lt_of_le_of_lt (Nat.le_max_right _ _) hk) θ wC wD wTs wTp wL wE _).2 hθ)

theorem outcome_TauTFTSim_vs_TauTFTSim_highθ :
    ∃ k₂, ∀ k, k₂ < k → ∀ θ wC wD wTs wTp wL wE, wC + wTs + wTp + wL < θ →
      ∃ N, outcome N (TauTFTSim k θ wC wD wTs wTp wL wE) (TauTFTSim k θ wC wD wTs wTp wL wE)
        = some (.D, .D) := by
  obtain ⟨k₂, h⟩ := tauTFTSim_phase
  refine ⟨k₂, fun k hk θ wC wD wTs wTp wL wE hθ => ?_⟩
  exact outcome_of_ex_plays
    ((h k hk θ wC wD wTs wTp wL wE _).2 hθ)
    ((h k hk θ wC wD wTs wTp wL wE _).2 hθ)

theorem outcome_TauTFTSim_vs_TauTFTPf_highθ :
    ∃ k₂, ∀ k, k₂ < k → ∀ θ wC wD wTs wTp wL wE, wC + wTs + wTp + wL < θ →
      ∃ N, outcome N (TauTFTSim k θ wC wD wTs wTp wL wE) (TauTFTPf k θ wC wD wTs wTp wL wE)
        = some (.D, .D) := by
  obtain ⟨k₁, h₁⟩ := tauTFTSim_phase
  obtain ⟨k₂, h₂⟩ := tauTFTPf_phase
  refine ⟨max k₁ k₂, fun k hk θ wC wD wTs wTp wL wE hθ => ?_⟩
  exact outcome_of_ex_plays
    ((h₁ k (lt_of_le_of_lt (Nat.le_max_left _ _) hk) θ wC wD wTs wTp wL wE _).2 hθ)
    ((h₂ k (lt_of_le_of_lt (Nat.le_max_right _ _) hk) θ wC wD wTs wTp wL wE _).2 hθ)

theorem outcome_TauTFTPf_vs_TauDupoc_highθ :
    ∃ k₂, ∀ k, k₂ < k → ∀ θ wC wD wTs wTp wL wE, wC + wTs + wTp + wL < θ →
      ∃ N, outcome N (TauTFTPf k θ wC wD wTs wTp wL wE) (TauDupoc k θ wC wD wTs wTp wL wE)
        = some (.D, .D) := by
  obtain ⟨k₁, h₁⟩ := tauTFTPf_phase
  obtain ⟨k₂, h₂⟩ := tauDupoc_phase
  refine ⟨max k₁ k₂, fun k hk θ wC wD wTs wTp wL wE hθ => ?_⟩
  exact outcome_of_ex_plays
    ((h₁ k (lt_of_le_of_lt (Nat.le_max_left _ _) hk) θ wC wD wTs wTp wL wE _).2 hθ)
    ((h₂ k (lt_of_le_of_lt (Nat.le_max_right _ _) hk) θ wC wD wTs wTp wL wE _).2 hθ)

theorem outcome_TauTFTPf_vs_TauTFTSim_highθ :
    ∃ k₂, ∀ k, k₂ < k → ∀ θ wC wD wTs wTp wL wE, wC + wTs + wTp + wL < θ →
      ∃ N, outcome N (TauTFTPf k θ wC wD wTs wTp wL wE) (TauTFTSim k θ wC wD wTs wTp wL wE)
        = some (.D, .D) := by
  obtain ⟨k₁, h₁⟩ := tauTFTPf_phase
  obtain ⟨k₂, h₂⟩ := tauTFTSim_phase
  refine ⟨max k₁ k₂, fun k hk θ wC wD wTs wTp wL wE hθ => ?_⟩
  exact outcome_of_ex_plays
    ((h₁ k (lt_of_le_of_lt (Nat.le_max_left _ _) hk) θ wC wD wTs wTp wL wE _).2 hθ)
    ((h₂ k (lt_of_le_of_lt (Nat.le_max_right _ _) hk) θ wC wD wTs wTp wL wE _).2 hθ)

theorem outcome_TauTFTPf_vs_TauTFTPf_highθ :
    ∃ k₂, ∀ k, k₂ < k → ∀ θ wC wD wTs wTp wL wE, wC + wTs + wTp + wL < θ →
      ∃ N, outcome N (TauTFTPf k θ wC wD wTs wTp wL wE) (TauTFTPf k θ wC wD wTs wTp wL wE)
        = some (.D, .D) := by
  obtain ⟨k₂, h⟩ := tauTFTPf_phase
  refine ⟨k₂, fun k hk θ wC wD wTs wTp wL wE hθ => ?_⟩
  exact outcome_of_ex_plays
    ((h k hk θ wC wD wTs wTp wL wE _).2 hθ)
    ((h k hk θ wC wD wTs wTp wL wE _).2 hθ)

/-! ## TauEBot cells — the SEPARATING bot (the window)

TauEBot's three regimes against everyone. The window cells are unsuffixed (its
cooperative regime); `_exploitθ` is the LOW-θ defection — where the lifted
exploiter defects against cooperators who cooperate with it, a non-monotone
profile no Def-3 (outcome-averaged) lift can express — and `_highθ` the shared
above-boundary defection. Note `outcome_TauDupoc_vs_TauEBot` in the window is
`(C, C)` even though TauDupoc CANNOT prove TauEBot's instance cooperates (the
floor): TauDupoc's cooperation is carried by the rest of its signal mass, not by
the EBot bit. -/

theorem outcome_TauEBot_vs_TauCooperate :
    ∃ k₂, ∀ k, k₂ < k → ∀ θ wC wD wTs wTp wL wE, wC < θ → θ ≤ wC + wTs + wTp + wL →
      ∃ N, outcome N (TauEBot k θ wC wD wTs wTp wL wE) TauCooperate
        = some (.C, .C) := by
  obtain ⟨k₂, h⟩ := tauEBot_phase
  refine ⟨k₂, fun k hk θ wC wD wTs wTp wL wE hθ₁ hθ₂ => ?_⟩
  exact outcome_of_ex_plays ((h k hk θ wC wD wTs wTp wL wE _).2.1 hθ₁ hθ₂) (tauCooperate_plays _)

theorem outcome_TauCooperate_vs_TauEBot :
    ∃ k₂, ∀ k, k₂ < k → ∀ θ wC wD wTs wTp wL wE, wC < θ → θ ≤ wC + wTs + wTp + wL →
      ∃ N, outcome N TauCooperate (TauEBot k θ wC wD wTs wTp wL wE)
        = some (.C, .C) := by
  obtain ⟨k₂, h⟩ := tauEBot_phase
  refine ⟨k₂, fun k hk θ wC wD wTs wTp wL wE hθ₁ hθ₂ => ?_⟩
  exact outcome_of_ex_plays (tauCooperate_plays _) ((h k hk θ wC wD wTs wTp wL wE _).2.1 hθ₁ hθ₂)

theorem outcome_TauEBot_vs_TauDefect :
    ∃ k₂, ∀ k, k₂ < k → ∀ θ wC wD wTs wTp wL wE, wC < θ → θ ≤ wC + wTs + wTp + wL →
      ∃ N, outcome N (TauEBot k θ wC wD wTs wTp wL wE) TauDefect
        = some (.C, .D) := by
  obtain ⟨k₂, h⟩ := tauEBot_phase
  refine ⟨k₂, fun k hk θ wC wD wTs wTp wL wE hθ₁ hθ₂ => ?_⟩
  exact outcome_of_ex_plays ((h k hk θ wC wD wTs wTp wL wE _).2.1 hθ₁ hθ₂) (tauDefect_plays _)

theorem outcome_TauDefect_vs_TauEBot :
    ∃ k₂, ∀ k, k₂ < k → ∀ θ wC wD wTs wTp wL wE, wC < θ → θ ≤ wC + wTs + wTp + wL →
      ∃ N, outcome N TauDefect (TauEBot k θ wC wD wTs wTp wL wE)
        = some (.D, .C) := by
  obtain ⟨k₂, h⟩ := tauEBot_phase
  refine ⟨k₂, fun k hk θ wC wD wTs wTp wL wE hθ₁ hθ₂ => ?_⟩
  exact outcome_of_ex_plays (tauDefect_plays _) ((h k hk θ wC wD wTs wTp wL wE _).2.1 hθ₁ hθ₂)

theorem outcome_TauEBot_vs_TauDupoc :
    ∃ k₂, ∀ k, k₂ < k → ∀ θ wC wD wTs wTp wL wE, wC < θ → θ ≤ wC + wTs + wTp + wL →
      ∃ N, outcome N (TauEBot k θ wC wD wTs wTp wL wE) (TauDupoc k θ wC wD wTs wTp wL wE)
        = some (.C, .C) := by
  obtain ⟨k₁, h₁⟩ := tauEBot_phase
  obtain ⟨k₂, h₂⟩ := tauDupoc_phase
  refine ⟨max k₁ k₂, fun k hk θ wC wD wTs wTp wL wE hθ₁ hθ₂ => ?_⟩
  exact outcome_of_ex_plays
    ((h₁ k (lt_of_le_of_lt (Nat.le_max_left _ _) hk) θ wC wD wTs wTp wL wE _).2.1 hθ₁ hθ₂)
    ((h₂ k (lt_of_le_of_lt (Nat.le_max_right _ _) hk) θ wC wD wTs wTp wL wE _).1 hθ₂)

theorem outcome_TauDupoc_vs_TauEBot :
    ∃ k₂, ∀ k, k₂ < k → ∀ θ wC wD wTs wTp wL wE, wC < θ → θ ≤ wC + wTs + wTp + wL →
      ∃ N, outcome N (TauDupoc k θ wC wD wTs wTp wL wE) (TauEBot k θ wC wD wTs wTp wL wE)
        = some (.C, .C) := by
  obtain ⟨k₁, h₁⟩ := tauDupoc_phase
  obtain ⟨k₂, h₂⟩ := tauEBot_phase
  refine ⟨max k₁ k₂, fun k hk θ wC wD wTs wTp wL wE hθ₁ hθ₂ => ?_⟩
  exact outcome_of_ex_plays
    ((h₁ k (lt_of_le_of_lt (Nat.le_max_left _ _) hk) θ wC wD wTs wTp wL wE _).1 hθ₂)
    ((h₂ k (lt_of_le_of_lt (Nat.le_max_right _ _) hk) θ wC wD wTs wTp wL wE _).2.1 hθ₁ hθ₂)

theorem outcome_TauEBot_vs_TauTFTSim :
    ∃ k₂, ∀ k, k₂ < k → ∀ θ wC wD wTs wTp wL wE, wC < θ → θ ≤ wC + wTs + wTp + wL →
      ∃ N, outcome N (TauEBot k θ wC wD wTs wTp wL wE) (TauTFTSim k θ wC wD wTs wTp wL wE)
        = some (.C, .C) := by
  obtain ⟨k₁, h₁⟩ := tauEBot_phase
  obtain ⟨k₂, h₂⟩ := tauTFTSim_phase
  refine ⟨max k₁ k₂, fun k hk θ wC wD wTs wTp wL wE hθ₁ hθ₂ => ?_⟩
  exact outcome_of_ex_plays
    ((h₁ k (lt_of_le_of_lt (Nat.le_max_left _ _) hk) θ wC wD wTs wTp wL wE _).2.1 hθ₁ hθ₂)
    ((h₂ k (lt_of_le_of_lt (Nat.le_max_right _ _) hk) θ wC wD wTs wTp wL wE _).1 hθ₂)

theorem outcome_TauTFTSim_vs_TauEBot :
    ∃ k₂, ∀ k, k₂ < k → ∀ θ wC wD wTs wTp wL wE, wC < θ → θ ≤ wC + wTs + wTp + wL →
      ∃ N, outcome N (TauTFTSim k θ wC wD wTs wTp wL wE) (TauEBot k θ wC wD wTs wTp wL wE)
        = some (.C, .C) := by
  obtain ⟨k₁, h₁⟩ := tauTFTSim_phase
  obtain ⟨k₂, h₂⟩ := tauEBot_phase
  refine ⟨max k₁ k₂, fun k hk θ wC wD wTs wTp wL wE hθ₁ hθ₂ => ?_⟩
  exact outcome_of_ex_plays
    ((h₁ k (lt_of_le_of_lt (Nat.le_max_left _ _) hk) θ wC wD wTs wTp wL wE _).1 hθ₂)
    ((h₂ k (lt_of_le_of_lt (Nat.le_max_right _ _) hk) θ wC wD wTs wTp wL wE _).2.1 hθ₁ hθ₂)

theorem outcome_TauEBot_vs_TauTFTPf :
    ∃ k₂, ∀ k, k₂ < k → ∀ θ wC wD wTs wTp wL wE, wC < θ → θ ≤ wC + wTs + wTp + wL →
      ∃ N, outcome N (TauEBot k θ wC wD wTs wTp wL wE) (TauTFTPf k θ wC wD wTs wTp wL wE)
        = some (.C, .C) := by
  obtain ⟨k₁, h₁⟩ := tauEBot_phase
  obtain ⟨k₂, h₂⟩ := tauTFTPf_phase
  refine ⟨max k₁ k₂, fun k hk θ wC wD wTs wTp wL wE hθ₁ hθ₂ => ?_⟩
  exact outcome_of_ex_plays
    ((h₁ k (lt_of_le_of_lt (Nat.le_max_left _ _) hk) θ wC wD wTs wTp wL wE _).2.1 hθ₁ hθ₂)
    ((h₂ k (lt_of_le_of_lt (Nat.le_max_right _ _) hk) θ wC wD wTs wTp wL wE _).1 hθ₂)

theorem outcome_TauTFTPf_vs_TauEBot :
    ∃ k₂, ∀ k, k₂ < k → ∀ θ wC wD wTs wTp wL wE, wC < θ → θ ≤ wC + wTs + wTp + wL →
      ∃ N, outcome N (TauTFTPf k θ wC wD wTs wTp wL wE) (TauEBot k θ wC wD wTs wTp wL wE)
        = some (.C, .C) := by
  obtain ⟨k₁, h₁⟩ := tauTFTPf_phase
  obtain ⟨k₂, h₂⟩ := tauEBot_phase
  refine ⟨max k₁ k₂, fun k hk θ wC wD wTs wTp wL wE hθ₁ hθ₂ => ?_⟩
  exact outcome_of_ex_plays
    ((h₁ k (lt_of_le_of_lt (Nat.le_max_left _ _) hk) θ wC wD wTs wTp wL wE _).1 hθ₂)
    ((h₂ k (lt_of_le_of_lt (Nat.le_max_right _ _) hk) θ wC wD wTs wTp wL wE _).2.1 hθ₁ hθ₂)

theorem outcome_TauEBot_vs_TauEBot :
    ∃ k₂, ∀ k, k₂ < k → ∀ θ wC wD wTs wTp wL wE, wC < θ → θ ≤ wC + wTs + wTp + wL →
      ∃ N, outcome N (TauEBot k θ wC wD wTs wTp wL wE) (TauEBot k θ wC wD wTs wTp wL wE)
        = some (.C, .C) := by
  obtain ⟨k₂, h⟩ := tauEBot_phase
  refine ⟨k₂, fun k hk θ wC wD wTs wTp wL wE hθ₁ hθ₂ => ?_⟩
  exact outcome_of_ex_plays
    ((h k hk θ wC wD wTs wTp wL wE _).2.1 hθ₁ hθ₂)
    ((h k hk θ wC wD wTs wTp wL wE _).2.1 hθ₁ hθ₂)

theorem outcome_TauEBot_vs_TauCooperate_exploitθ :
    ∃ k₂, ∀ k, k₂ < k → ∀ θ wC wD wTs wTp wL wE, θ ≤ wC →
      ∃ N, outcome N (TauEBot k θ wC wD wTs wTp wL wE) TauCooperate
        = some (.D, .C) := by
  obtain ⟨k₂, h⟩ := tauEBot_phase
  refine ⟨k₂, fun k hk θ wC wD wTs wTp wL wE hθ => ?_⟩
  exact outcome_of_ex_plays ((h k hk θ wC wD wTs wTp wL wE _).1 hθ) (tauCooperate_plays _)

theorem outcome_TauCooperate_vs_TauEBot_exploitθ :
    ∃ k₂, ∀ k, k₂ < k → ∀ θ wC wD wTs wTp wL wE, θ ≤ wC →
      ∃ N, outcome N TauCooperate (TauEBot k θ wC wD wTs wTp wL wE)
        = some (.C, .D) := by
  obtain ⟨k₂, h⟩ := tauEBot_phase
  refine ⟨k₂, fun k hk θ wC wD wTs wTp wL wE hθ => ?_⟩
  exact outcome_of_ex_plays (tauCooperate_plays _) ((h k hk θ wC wD wTs wTp wL wE _).1 hθ)

theorem outcome_TauEBot_vs_TauDefect_exploitθ :
    ∃ k₂, ∀ k, k₂ < k → ∀ θ wC wD wTs wTp wL wE, θ ≤ wC →
      ∃ N, outcome N (TauEBot k θ wC wD wTs wTp wL wE) TauDefect
        = some (.D, .D) := by
  obtain ⟨k₂, h⟩ := tauEBot_phase
  refine ⟨k₂, fun k hk θ wC wD wTs wTp wL wE hθ => ?_⟩
  exact outcome_of_ex_plays ((h k hk θ wC wD wTs wTp wL wE _).1 hθ) (tauDefect_plays _)

theorem outcome_TauDefect_vs_TauEBot_exploitθ :
    ∃ k₂, ∀ k, k₂ < k → ∀ θ wC wD wTs wTp wL wE, θ ≤ wC →
      ∃ N, outcome N TauDefect (TauEBot k θ wC wD wTs wTp wL wE)
        = some (.D, .D) := by
  obtain ⟨k₂, h⟩ := tauEBot_phase
  refine ⟨k₂, fun k hk θ wC wD wTs wTp wL wE hθ => ?_⟩
  exact outcome_of_ex_plays (tauDefect_plays _) ((h k hk θ wC wD wTs wTp wL wE _).1 hθ)

theorem outcome_TauEBot_vs_TauDupoc_exploitθ :
    ∃ k₂, ∀ k, k₂ < k → ∀ θ wC wD wTs wTp wL wE, θ ≤ wC →
      ∃ N, outcome N (TauEBot k θ wC wD wTs wTp wL wE) (TauDupoc k θ wC wD wTs wTp wL wE)
        = some (.D, .C) := by
  obtain ⟨k₁, h₁⟩ := tauEBot_phase
  obtain ⟨k₂, h₂⟩ := tauDupoc_phase
  refine ⟨max k₁ k₂, fun k hk θ wC wD wTs wTp wL wE hθ => ?_⟩
  have hθ' : θ ≤ wC + wTs + wTp + wL := by omega
  exact outcome_of_ex_plays
    ((h₁ k (lt_of_le_of_lt (Nat.le_max_left _ _) hk) θ wC wD wTs wTp wL wE _).1 hθ)
    ((h₂ k (lt_of_le_of_lt (Nat.le_max_right _ _) hk) θ wC wD wTs wTp wL wE _).1 hθ')

theorem outcome_TauDupoc_vs_TauEBot_exploitθ :
    ∃ k₂, ∀ k, k₂ < k → ∀ θ wC wD wTs wTp wL wE, θ ≤ wC →
      ∃ N, outcome N (TauDupoc k θ wC wD wTs wTp wL wE) (TauEBot k θ wC wD wTs wTp wL wE)
        = some (.C, .D) := by
  obtain ⟨k₁, h₁⟩ := tauDupoc_phase
  obtain ⟨k₂, h₂⟩ := tauEBot_phase
  refine ⟨max k₁ k₂, fun k hk θ wC wD wTs wTp wL wE hθ => ?_⟩
  have hθ' : θ ≤ wC + wTs + wTp + wL := by omega
  exact outcome_of_ex_plays
    ((h₁ k (lt_of_le_of_lt (Nat.le_max_left _ _) hk) θ wC wD wTs wTp wL wE _).1 hθ')
    ((h₂ k (lt_of_le_of_lt (Nat.le_max_right _ _) hk) θ wC wD wTs wTp wL wE _).1 hθ)

theorem outcome_TauEBot_vs_TauTFTSim_exploitθ :
    ∃ k₂, ∀ k, k₂ < k → ∀ θ wC wD wTs wTp wL wE, θ ≤ wC →
      ∃ N, outcome N (TauEBot k θ wC wD wTs wTp wL wE) (TauTFTSim k θ wC wD wTs wTp wL wE)
        = some (.D, .C) := by
  obtain ⟨k₁, h₁⟩ := tauEBot_phase
  obtain ⟨k₂, h₂⟩ := tauTFTSim_phase
  refine ⟨max k₁ k₂, fun k hk θ wC wD wTs wTp wL wE hθ => ?_⟩
  have hθ' : θ ≤ wC + wTs + wTp + wL := by omega
  exact outcome_of_ex_plays
    ((h₁ k (lt_of_le_of_lt (Nat.le_max_left _ _) hk) θ wC wD wTs wTp wL wE _).1 hθ)
    ((h₂ k (lt_of_le_of_lt (Nat.le_max_right _ _) hk) θ wC wD wTs wTp wL wE _).1 hθ')

theorem outcome_TauTFTSim_vs_TauEBot_exploitθ :
    ∃ k₂, ∀ k, k₂ < k → ∀ θ wC wD wTs wTp wL wE, θ ≤ wC →
      ∃ N, outcome N (TauTFTSim k θ wC wD wTs wTp wL wE) (TauEBot k θ wC wD wTs wTp wL wE)
        = some (.C, .D) := by
  obtain ⟨k₁, h₁⟩ := tauTFTSim_phase
  obtain ⟨k₂, h₂⟩ := tauEBot_phase
  refine ⟨max k₁ k₂, fun k hk θ wC wD wTs wTp wL wE hθ => ?_⟩
  have hθ' : θ ≤ wC + wTs + wTp + wL := by omega
  exact outcome_of_ex_plays
    ((h₁ k (lt_of_le_of_lt (Nat.le_max_left _ _) hk) θ wC wD wTs wTp wL wE _).1 hθ')
    ((h₂ k (lt_of_le_of_lt (Nat.le_max_right _ _) hk) θ wC wD wTs wTp wL wE _).1 hθ)

theorem outcome_TauEBot_vs_TauTFTPf_exploitθ :
    ∃ k₂, ∀ k, k₂ < k → ∀ θ wC wD wTs wTp wL wE, θ ≤ wC →
      ∃ N, outcome N (TauEBot k θ wC wD wTs wTp wL wE) (TauTFTPf k θ wC wD wTs wTp wL wE)
        = some (.D, .C) := by
  obtain ⟨k₁, h₁⟩ := tauEBot_phase
  obtain ⟨k₂, h₂⟩ := tauTFTPf_phase
  refine ⟨max k₁ k₂, fun k hk θ wC wD wTs wTp wL wE hθ => ?_⟩
  have hθ' : θ ≤ wC + wTs + wTp + wL := by omega
  exact outcome_of_ex_plays
    ((h₁ k (lt_of_le_of_lt (Nat.le_max_left _ _) hk) θ wC wD wTs wTp wL wE _).1 hθ)
    ((h₂ k (lt_of_le_of_lt (Nat.le_max_right _ _) hk) θ wC wD wTs wTp wL wE _).1 hθ')

theorem outcome_TauTFTPf_vs_TauEBot_exploitθ :
    ∃ k₂, ∀ k, k₂ < k → ∀ θ wC wD wTs wTp wL wE, θ ≤ wC →
      ∃ N, outcome N (TauTFTPf k θ wC wD wTs wTp wL wE) (TauEBot k θ wC wD wTs wTp wL wE)
        = some (.C, .D) := by
  obtain ⟨k₁, h₁⟩ := tauTFTPf_phase
  obtain ⟨k₂, h₂⟩ := tauEBot_phase
  refine ⟨max k₁ k₂, fun k hk θ wC wD wTs wTp wL wE hθ => ?_⟩
  have hθ' : θ ≤ wC + wTs + wTp + wL := by omega
  exact outcome_of_ex_plays
    ((h₁ k (lt_of_le_of_lt (Nat.le_max_left _ _) hk) θ wC wD wTs wTp wL wE _).1 hθ')
    ((h₂ k (lt_of_le_of_lt (Nat.le_max_right _ _) hk) θ wC wD wTs wTp wL wE _).1 hθ)

theorem outcome_TauEBot_vs_TauEBot_exploitθ :
    ∃ k₂, ∀ k, k₂ < k → ∀ θ wC wD wTs wTp wL wE, θ ≤ wC →
      ∃ N, outcome N (TauEBot k θ wC wD wTs wTp wL wE) (TauEBot k θ wC wD wTs wTp wL wE)
        = some (.D, .D) := by
  obtain ⟨k₂, h⟩ := tauEBot_phase
  refine ⟨k₂, fun k hk θ wC wD wTs wTp wL wE hθ => ?_⟩
  exact outcome_of_ex_plays
    ((h k hk θ wC wD wTs wTp wL wE _).1 hθ)
    ((h k hk θ wC wD wTs wTp wL wE _).1 hθ)

theorem outcome_TauEBot_vs_TauCooperate_highθ :
    ∃ k₂, ∀ k, k₂ < k → ∀ θ wC wD wTs wTp wL wE, wC + wTs + wTp + wL < θ →
      ∃ N, outcome N (TauEBot k θ wC wD wTs wTp wL wE) TauCooperate
        = some (.D, .C) := by
  obtain ⟨k₂, h⟩ := tauEBot_phase
  refine ⟨k₂, fun k hk θ wC wD wTs wTp wL wE hθ => ?_⟩
  exact outcome_of_ex_plays ((h k hk θ wC wD wTs wTp wL wE _).2.2 hθ) (tauCooperate_plays _)

theorem outcome_TauCooperate_vs_TauEBot_highθ :
    ∃ k₂, ∀ k, k₂ < k → ∀ θ wC wD wTs wTp wL wE, wC + wTs + wTp + wL < θ →
      ∃ N, outcome N TauCooperate (TauEBot k θ wC wD wTs wTp wL wE)
        = some (.C, .D) := by
  obtain ⟨k₂, h⟩ := tauEBot_phase
  refine ⟨k₂, fun k hk θ wC wD wTs wTp wL wE hθ => ?_⟩
  exact outcome_of_ex_plays (tauCooperate_plays _) ((h k hk θ wC wD wTs wTp wL wE _).2.2 hθ)

theorem outcome_TauEBot_vs_TauDefect_highθ :
    ∃ k₂, ∀ k, k₂ < k → ∀ θ wC wD wTs wTp wL wE, wC + wTs + wTp + wL < θ →
      ∃ N, outcome N (TauEBot k θ wC wD wTs wTp wL wE) TauDefect
        = some (.D, .D) := by
  obtain ⟨k₂, h⟩ := tauEBot_phase
  refine ⟨k₂, fun k hk θ wC wD wTs wTp wL wE hθ => ?_⟩
  exact outcome_of_ex_plays ((h k hk θ wC wD wTs wTp wL wE _).2.2 hθ) (tauDefect_plays _)

theorem outcome_TauDefect_vs_TauEBot_highθ :
    ∃ k₂, ∀ k, k₂ < k → ∀ θ wC wD wTs wTp wL wE, wC + wTs + wTp + wL < θ →
      ∃ N, outcome N TauDefect (TauEBot k θ wC wD wTs wTp wL wE)
        = some (.D, .D) := by
  obtain ⟨k₂, h⟩ := tauEBot_phase
  refine ⟨k₂, fun k hk θ wC wD wTs wTp wL wE hθ => ?_⟩
  exact outcome_of_ex_plays (tauDefect_plays _) ((h k hk θ wC wD wTs wTp wL wE _).2.2 hθ)

theorem outcome_TauEBot_vs_TauDupoc_highθ :
    ∃ k₂, ∀ k, k₂ < k → ∀ θ wC wD wTs wTp wL wE, wC + wTs + wTp + wL < θ →
      ∃ N, outcome N (TauEBot k θ wC wD wTs wTp wL wE) (TauDupoc k θ wC wD wTs wTp wL wE)
        = some (.D, .D) := by
  obtain ⟨k₁, h₁⟩ := tauEBot_phase
  obtain ⟨k₂, h₂⟩ := tauDupoc_phase
  refine ⟨max k₁ k₂, fun k hk θ wC wD wTs wTp wL wE hθ => ?_⟩
  exact outcome_of_ex_plays
    ((h₁ k (lt_of_le_of_lt (Nat.le_max_left _ _) hk) θ wC wD wTs wTp wL wE _).2.2 hθ)
    ((h₂ k (lt_of_le_of_lt (Nat.le_max_right _ _) hk) θ wC wD wTs wTp wL wE _).2 hθ)

theorem outcome_TauDupoc_vs_TauEBot_highθ :
    ∃ k₂, ∀ k, k₂ < k → ∀ θ wC wD wTs wTp wL wE, wC + wTs + wTp + wL < θ →
      ∃ N, outcome N (TauDupoc k θ wC wD wTs wTp wL wE) (TauEBot k θ wC wD wTs wTp wL wE)
        = some (.D, .D) := by
  obtain ⟨k₁, h₁⟩ := tauDupoc_phase
  obtain ⟨k₂, h₂⟩ := tauEBot_phase
  refine ⟨max k₁ k₂, fun k hk θ wC wD wTs wTp wL wE hθ => ?_⟩
  exact outcome_of_ex_plays
    ((h₁ k (lt_of_le_of_lt (Nat.le_max_left _ _) hk) θ wC wD wTs wTp wL wE _).2 hθ)
    ((h₂ k (lt_of_le_of_lt (Nat.le_max_right _ _) hk) θ wC wD wTs wTp wL wE _).2.2 hθ)

theorem outcome_TauEBot_vs_TauTFTSim_highθ :
    ∃ k₂, ∀ k, k₂ < k → ∀ θ wC wD wTs wTp wL wE, wC + wTs + wTp + wL < θ →
      ∃ N, outcome N (TauEBot k θ wC wD wTs wTp wL wE) (TauTFTSim k θ wC wD wTs wTp wL wE)
        = some (.D, .D) := by
  obtain ⟨k₁, h₁⟩ := tauEBot_phase
  obtain ⟨k₂, h₂⟩ := tauTFTSim_phase
  refine ⟨max k₁ k₂, fun k hk θ wC wD wTs wTp wL wE hθ => ?_⟩
  exact outcome_of_ex_plays
    ((h₁ k (lt_of_le_of_lt (Nat.le_max_left _ _) hk) θ wC wD wTs wTp wL wE _).2.2 hθ)
    ((h₂ k (lt_of_le_of_lt (Nat.le_max_right _ _) hk) θ wC wD wTs wTp wL wE _).2 hθ)

theorem outcome_TauTFTSim_vs_TauEBot_highθ :
    ∃ k₂, ∀ k, k₂ < k → ∀ θ wC wD wTs wTp wL wE, wC + wTs + wTp + wL < θ →
      ∃ N, outcome N (TauTFTSim k θ wC wD wTs wTp wL wE) (TauEBot k θ wC wD wTs wTp wL wE)
        = some (.D, .D) := by
  obtain ⟨k₁, h₁⟩ := tauTFTSim_phase
  obtain ⟨k₂, h₂⟩ := tauEBot_phase
  refine ⟨max k₁ k₂, fun k hk θ wC wD wTs wTp wL wE hθ => ?_⟩
  exact outcome_of_ex_plays
    ((h₁ k (lt_of_le_of_lt (Nat.le_max_left _ _) hk) θ wC wD wTs wTp wL wE _).2 hθ)
    ((h₂ k (lt_of_le_of_lt (Nat.le_max_right _ _) hk) θ wC wD wTs wTp wL wE _).2.2 hθ)

theorem outcome_TauEBot_vs_TauTFTPf_highθ :
    ∃ k₂, ∀ k, k₂ < k → ∀ θ wC wD wTs wTp wL wE, wC + wTs + wTp + wL < θ →
      ∃ N, outcome N (TauEBot k θ wC wD wTs wTp wL wE) (TauTFTPf k θ wC wD wTs wTp wL wE)
        = some (.D, .D) := by
  obtain ⟨k₁, h₁⟩ := tauEBot_phase
  obtain ⟨k₂, h₂⟩ := tauTFTPf_phase
  refine ⟨max k₁ k₂, fun k hk θ wC wD wTs wTp wL wE hθ => ?_⟩
  exact outcome_of_ex_plays
    ((h₁ k (lt_of_le_of_lt (Nat.le_max_left _ _) hk) θ wC wD wTs wTp wL wE _).2.2 hθ)
    ((h₂ k (lt_of_le_of_lt (Nat.le_max_right _ _) hk) θ wC wD wTs wTp wL wE _).2 hθ)

theorem outcome_TauTFTPf_vs_TauEBot_highθ :
    ∃ k₂, ∀ k, k₂ < k → ∀ θ wC wD wTs wTp wL wE, wC + wTs + wTp + wL < θ →
      ∃ N, outcome N (TauTFTPf k θ wC wD wTs wTp wL wE) (TauEBot k θ wC wD wTs wTp wL wE)
        = some (.D, .D) := by
  obtain ⟨k₁, h₁⟩ := tauTFTPf_phase
  obtain ⟨k₂, h₂⟩ := tauEBot_phase
  refine ⟨max k₁ k₂, fun k hk θ wC wD wTs wTp wL wE hθ => ?_⟩
  exact outcome_of_ex_plays
    ((h₁ k (lt_of_le_of_lt (Nat.le_max_left _ _) hk) θ wC wD wTs wTp wL wE _).2 hθ)
    ((h₂ k (lt_of_le_of_lt (Nat.le_max_right _ _) hk) θ wC wD wTs wTp wL wE _).2.2 hθ)

theorem outcome_TauEBot_vs_TauEBot_highθ :
    ∃ k₂, ∀ k, k₂ < k → ∀ θ wC wD wTs wTp wL wE, wC + wTs + wTp + wL < θ →
      ∃ N, outcome N (TauEBot k θ wC wD wTs wTp wL wE) (TauEBot k θ wC wD wTs wTp wL wE)
        = some (.D, .D) := by
  obtain ⟨k₂, h⟩ := tauEBot_phase
  refine ⟨k₂, fun k hk θ wC wD wTs wTp wL wE hθ => ?_⟩
  exact outcome_of_ex_plays
    ((h k hk θ wC wD wTs wTp wL wE _).2.2 hθ)
    ((h k hk θ wC wD wTs wTp wL wE _).2.2 hθ)

end PD.Theorems.Tau
