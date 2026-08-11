import PrisonersDilemma.Tau.Phases

/-!
# Theorems/Tau/Matrix — the Def-4 outcome matrix (milestone 1)

The 25 ordered outcomes of the 5-bot tau zoo in the COOPERATIVE regime
(`θ ≤ wC + wTs + wTp + wL` — the threshold within the cooperation mass), plus the
three defect-regime self-plays exhibiting the α-flip. All corollaries of the phase
theorems (`Tau/Phases`): tau players are `.opp`-free, hence extensionally constant,
so the matrix is the product of the play vector with itself — each cell is one
`outcome_of_ex_plays`.

Notable cells: the θ-bots cooperate even AGAINST TauDefect — `(C, D)` exploitation.
That is correct Def-4 semantics: a tau player acts on its SIGNAL, and a wrong signal
costs payoff. Partial transparency has a price, and these cells are it.

(Single-file layout, deviating from the per-pair convention: tau cells are not
base-matrix cells — no sheet sync — and the plays are opponent-independent, so 25
stub files would be noise.)
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

/-! ## TauDupoc rows/columns -/

theorem outcome_TauDupoc_vs_TauCooperate :
    ∃ k₂, ∀ k, k₂ < k → ∀ θ wC wD wTs wTp wL, θ ≤ wC + wTs + wTp + wL →
      ∃ N, outcome N (TauDupoc k θ wC wD wTs wTp wL) TauCooperate = some (.C, .C) := by
  obtain ⟨k₂, h⟩ := tauDupoc_phase
  exact ⟨k₂, fun k hk θ wC wD wTs wTp wL hθ =>
    outcome_of_ex_plays ((h k hk θ wC wD wTs wTp wL _).1 hθ) (tauCooperate_plays _)⟩

theorem outcome_TauCooperate_vs_TauDupoc :
    ∃ k₂, ∀ k, k₂ < k → ∀ θ wC wD wTs wTp wL, θ ≤ wC + wTs + wTp + wL →
      ∃ N, outcome N TauCooperate (TauDupoc k θ wC wD wTs wTp wL) = some (.C, .C) := by
  obtain ⟨k₂, h⟩ := tauDupoc_phase
  exact ⟨k₂, fun k hk θ wC wD wTs wTp wL hθ =>
    outcome_of_ex_plays (tauCooperate_plays _) ((h k hk θ wC wD wTs wTp wL _).1 hθ)⟩

/-- The exploitation cell: a cooperate-weighted signal against the actual TauDefect —
    the θ-bot pays for its wrong beliefs. -/
theorem outcome_TauDupoc_vs_TauDefect :
    ∃ k₂, ∀ k, k₂ < k → ∀ θ wC wD wTs wTp wL, θ ≤ wC + wTs + wTp + wL →
      ∃ N, outcome N (TauDupoc k θ wC wD wTs wTp wL) TauDefect = some (.C, .D) := by
  obtain ⟨k₂, h⟩ := tauDupoc_phase
  exact ⟨k₂, fun k hk θ wC wD wTs wTp wL hθ =>
    outcome_of_ex_plays ((h k hk θ wC wD wTs wTp wL _).1 hθ) (tauDefect_plays _)⟩

theorem outcome_TauDefect_vs_TauDupoc :
    ∃ k₂, ∀ k, k₂ < k → ∀ θ wC wD wTs wTp wL, θ ≤ wC + wTs + wTp + wL →
      ∃ N, outcome N TauDefect (TauDupoc k θ wC wD wTs wTp wL) = some (.D, .C) := by
  obtain ⟨k₂, h⟩ := tauDupoc_phase
  exact ⟨k₂, fun k hk θ wC wD wTs wTp wL hθ =>
    outcome_of_ex_plays (tauDefect_plays _) ((h k hk θ wC wD wTs wTp wL _).1 hθ)⟩

/-- **Löbian self-cooperation, Def-4 edition**: TauDupoc vs itself is `(C, C)` in the
    cooperative regime — via the quine fixpoint bit, not via reading the opponent. -/
theorem outcome_TauDupoc_vs_TauDupoc :
    ∃ k₂, ∀ k, k₂ < k → ∀ θ wC wD wTs wTp wL, θ ≤ wC + wTs + wTp + wL →
      ∃ N, outcome N (TauDupoc k θ wC wD wTs wTp wL) (TauDupoc k θ wC wD wTs wTp wL)
        = some (.C, .C) := by
  obtain ⟨k₂, h⟩ := tauDupoc_phase
  exact ⟨k₂, fun k hk θ wC wD wTs wTp wL hθ =>
    outcome_of_ex_plays ((h k hk θ wC wD wTs wTp wL _).1 hθ)
      ((h k hk θ wC wD wTs wTp wL _).1 hθ)⟩

/-! ## TauTFTSim rows/columns -/

theorem outcome_TauTFTSim_vs_TauCooperate :
    ∃ k₂, ∀ k, k₂ < k → ∀ θ wC wD wTs wTp wL, θ ≤ wC + wTs + wTp + wL →
      ∃ N, outcome N (TauTFTSim k θ wC wD wTs wTp wL) TauCooperate = some (.C, .C) := by
  obtain ⟨k₂, h⟩ := tauTFTSim_phase
  exact ⟨k₂, fun k hk θ wC wD wTs wTp wL hθ =>
    outcome_of_ex_plays ((h k hk θ wC wD wTs wTp wL _).1 hθ) (tauCooperate_plays _)⟩

theorem outcome_TauCooperate_vs_TauTFTSim :
    ∃ k₂, ∀ k, k₂ < k → ∀ θ wC wD wTs wTp wL, θ ≤ wC + wTs + wTp + wL →
      ∃ N, outcome N TauCooperate (TauTFTSim k θ wC wD wTs wTp wL) = some (.C, .C) := by
  obtain ⟨k₂, h⟩ := tauTFTSim_phase
  exact ⟨k₂, fun k hk θ wC wD wTs wTp wL hθ =>
    outcome_of_ex_plays (tauCooperate_plays _) ((h k hk θ wC wD wTs wTp wL _).1 hθ)⟩

theorem outcome_TauTFTSim_vs_TauDefect :
    ∃ k₂, ∀ k, k₂ < k → ∀ θ wC wD wTs wTp wL, θ ≤ wC + wTs + wTp + wL →
      ∃ N, outcome N (TauTFTSim k θ wC wD wTs wTp wL) TauDefect = some (.C, .D) := by
  obtain ⟨k₂, h⟩ := tauTFTSim_phase
  exact ⟨k₂, fun k hk θ wC wD wTs wTp wL hθ =>
    outcome_of_ex_plays ((h k hk θ wC wD wTs wTp wL _).1 hθ) (tauDefect_plays _)⟩

theorem outcome_TauDefect_vs_TauTFTSim :
    ∃ k₂, ∀ k, k₂ < k → ∀ θ wC wD wTs wTp wL, θ ≤ wC + wTs + wTp + wL →
      ∃ N, outcome N TauDefect (TauTFTSim k θ wC wD wTs wTp wL) = some (.D, .C) := by
  obtain ⟨k₂, h⟩ := tauTFTSim_phase
  exact ⟨k₂, fun k hk θ wC wD wTs wTp wL hθ =>
    outcome_of_ex_plays (tauDefect_plays _) ((h k hk θ wC wD wTs wTp wL _).1 hθ)⟩

theorem outcome_TauTFTSim_vs_TauTFTSim :
    ∃ k₂, ∀ k, k₂ < k → ∀ θ wC wD wTs wTp wL, θ ≤ wC + wTs + wTp + wL →
      ∃ N, outcome N (TauTFTSim k θ wC wD wTs wTp wL) (TauTFTSim k θ wC wD wTs wTp wL)
        = some (.C, .C) := by
  obtain ⟨k₂, h⟩ := tauTFTSim_phase
  exact ⟨k₂, fun k hk θ wC wD wTs wTp wL hθ =>
    outcome_of_ex_plays ((h k hk θ wC wD wTs wTp wL _).1 hθ)
      ((h k hk θ wC wD wTs wTp wL _).1 hθ)⟩

/-! ## TauTFTPf rows/columns -/

theorem outcome_TauTFTPf_vs_TauCooperate :
    ∃ k₂, ∀ k, k₂ < k → ∀ θ wC wD wTs wTp wL, θ ≤ wC + wTs + wTp + wL →
      ∃ N, outcome N (TauTFTPf k θ wC wD wTs wTp wL) TauCooperate = some (.C, .C) := by
  obtain ⟨k₂, h⟩ := tauTFTPf_phase
  exact ⟨k₂, fun k hk θ wC wD wTs wTp wL hθ =>
    outcome_of_ex_plays ((h k hk θ wC wD wTs wTp wL _).1 hθ) (tauCooperate_plays _)⟩

theorem outcome_TauCooperate_vs_TauTFTPf :
    ∃ k₂, ∀ k, k₂ < k → ∀ θ wC wD wTs wTp wL, θ ≤ wC + wTs + wTp + wL →
      ∃ N, outcome N TauCooperate (TauTFTPf k θ wC wD wTs wTp wL) = some (.C, .C) := by
  obtain ⟨k₂, h⟩ := tauTFTPf_phase
  exact ⟨k₂, fun k hk θ wC wD wTs wTp wL hθ =>
    outcome_of_ex_plays (tauCooperate_plays _) ((h k hk θ wC wD wTs wTp wL _).1 hθ)⟩

theorem outcome_TauTFTPf_vs_TauDefect :
    ∃ k₂, ∀ k, k₂ < k → ∀ θ wC wD wTs wTp wL, θ ≤ wC + wTs + wTp + wL →
      ∃ N, outcome N (TauTFTPf k θ wC wD wTs wTp wL) TauDefect = some (.C, .D) := by
  obtain ⟨k₂, h⟩ := tauTFTPf_phase
  exact ⟨k₂, fun k hk θ wC wD wTs wTp wL hθ =>
    outcome_of_ex_plays ((h k hk θ wC wD wTs wTp wL _).1 hθ) (tauDefect_plays _)⟩

theorem outcome_TauDefect_vs_TauTFTPf :
    ∃ k₂, ∀ k, k₂ < k → ∀ θ wC wD wTs wTp wL, θ ≤ wC + wTs + wTp + wL →
      ∃ N, outcome N TauDefect (TauTFTPf k θ wC wD wTs wTp wL) = some (.D, .C) := by
  obtain ⟨k₂, h⟩ := tauTFTPf_phase
  exact ⟨k₂, fun k hk θ wC wD wTs wTp wL hθ =>
    outcome_of_ex_plays (tauDefect_plays _) ((h k hk θ wC wD wTs wTp wL _).1 hθ)⟩

theorem outcome_TauTFTPf_vs_TauTFTPf :
    ∃ k₂, ∀ k, k₂ < k → ∀ θ wC wD wTs wTp wL, θ ≤ wC + wTs + wTp + wL →
      ∃ N, outcome N (TauTFTPf k θ wC wD wTs wTp wL) (TauTFTPf k θ wC wD wTs wTp wL)
        = some (.C, .C) := by
  obtain ⟨k₂, h⟩ := tauTFTPf_phase
  exact ⟨k₂, fun k hk θ wC wD wTs wTp wL hθ =>
    outcome_of_ex_plays ((h k hk θ wC wD wTs wTp wL _).1 hθ)
      ((h k hk θ wC wD wTs wTp wL _).1 hθ)⟩

/-! ## Mixed θ-bot pairs -/

theorem outcome_TauDupoc_vs_TauTFTSim :
    ∃ k₂, ∀ k, k₂ < k → ∀ θ wC wD wTs wTp wL, θ ≤ wC + wTs + wTp + wL →
      ∃ N, outcome N (TauDupoc k θ wC wD wTs wTp wL) (TauTFTSim k θ wC wD wTs wTp wL)
        = some (.C, .C) := by
  obtain ⟨k₁, h₁⟩ := tauDupoc_phase
  obtain ⟨k₂, h₂⟩ := tauTFTSim_phase
  refine ⟨max k₁ k₂, fun k hk θ wC wD wTs wTp wL hθ => ?_⟩
  exact outcome_of_ex_plays
    ((h₁ k (lt_of_le_of_lt (Nat.le_max_left _ _) hk) θ wC wD wTs wTp wL _).1 hθ)
    ((h₂ k (lt_of_le_of_lt (Nat.le_max_right _ _) hk) θ wC wD wTs wTp wL _).1 hθ)

theorem outcome_TauTFTSim_vs_TauDupoc :
    ∃ k₂, ∀ k, k₂ < k → ∀ θ wC wD wTs wTp wL, θ ≤ wC + wTs + wTp + wL →
      ∃ N, outcome N (TauTFTSim k θ wC wD wTs wTp wL) (TauDupoc k θ wC wD wTs wTp wL)
        = some (.C, .C) := by
  obtain ⟨k₁, h₁⟩ := tauTFTSim_phase
  obtain ⟨k₂, h₂⟩ := tauDupoc_phase
  refine ⟨max k₁ k₂, fun k hk θ wC wD wTs wTp wL hθ => ?_⟩
  exact outcome_of_ex_plays
    ((h₁ k (lt_of_le_of_lt (Nat.le_max_left _ _) hk) θ wC wD wTs wTp wL _).1 hθ)
    ((h₂ k (lt_of_le_of_lt (Nat.le_max_right _ _) hk) θ wC wD wTs wTp wL _).1 hθ)

theorem outcome_TauDupoc_vs_TauTFTPf :
    ∃ k₂, ∀ k, k₂ < k → ∀ θ wC wD wTs wTp wL, θ ≤ wC + wTs + wTp + wL →
      ∃ N, outcome N (TauDupoc k θ wC wD wTs wTp wL) (TauTFTPf k θ wC wD wTs wTp wL)
        = some (.C, .C) := by
  obtain ⟨k₁, h₁⟩ := tauDupoc_phase
  obtain ⟨k₂, h₂⟩ := tauTFTPf_phase
  refine ⟨max k₁ k₂, fun k hk θ wC wD wTs wTp wL hθ => ?_⟩
  exact outcome_of_ex_plays
    ((h₁ k (lt_of_le_of_lt (Nat.le_max_left _ _) hk) θ wC wD wTs wTp wL _).1 hθ)
    ((h₂ k (lt_of_le_of_lt (Nat.le_max_right _ _) hk) θ wC wD wTs wTp wL _).1 hθ)

theorem outcome_TauTFTPf_vs_TauDupoc :
    ∃ k₂, ∀ k, k₂ < k → ∀ θ wC wD wTs wTp wL, θ ≤ wC + wTs + wTp + wL →
      ∃ N, outcome N (TauTFTPf k θ wC wD wTs wTp wL) (TauDupoc k θ wC wD wTs wTp wL)
        = some (.C, .C) := by
  obtain ⟨k₁, h₁⟩ := tauTFTPf_phase
  obtain ⟨k₂, h₂⟩ := tauDupoc_phase
  refine ⟨max k₁ k₂, fun k hk θ wC wD wTs wTp wL hθ => ?_⟩
  exact outcome_of_ex_plays
    ((h₁ k (lt_of_le_of_lt (Nat.le_max_left _ _) hk) θ wC wD wTs wTp wL _).1 hθ)
    ((h₂ k (lt_of_le_of_lt (Nat.le_max_right _ _) hk) θ wC wD wTs wTp wL _).1 hθ)

theorem outcome_TauTFTSim_vs_TauTFTPf :
    ∃ k₂, ∀ k, k₂ < k → ∀ θ wC wD wTs wTp wL, θ ≤ wC + wTs + wTp + wL →
      ∃ N, outcome N (TauTFTSim k θ wC wD wTs wTp wL) (TauTFTPf k θ wC wD wTs wTp wL)
        = some (.C, .C) := by
  obtain ⟨k₁, h₁⟩ := tauTFTSim_phase
  obtain ⟨k₂, h₂⟩ := tauTFTPf_phase
  refine ⟨max k₁ k₂, fun k hk θ wC wD wTs wTp wL hθ => ?_⟩
  exact outcome_of_ex_plays
    ((h₁ k (lt_of_le_of_lt (Nat.le_max_left _ _) hk) θ wC wD wTs wTp wL _).1 hθ)
    ((h₂ k (lt_of_le_of_lt (Nat.le_max_right _ _) hk) θ wC wD wTs wTp wL _).1 hθ)

theorem outcome_TauTFTPf_vs_TauTFTSim :
    ∃ k₂, ∀ k, k₂ < k → ∀ θ wC wD wTs wTp wL, θ ≤ wC + wTs + wTp + wL →
      ∃ N, outcome N (TauTFTPf k θ wC wD wTs wTp wL) (TauTFTSim k θ wC wD wTs wTp wL)
        = some (.C, .C) := by
  obtain ⟨k₁, h₁⟩ := tauTFTPf_phase
  obtain ⟨k₂, h₂⟩ := tauTFTSim_phase
  refine ⟨max k₁ k₂, fun k hk θ wC wD wTs wTp wL hθ => ?_⟩
  exact outcome_of_ex_plays
    ((h₁ k (lt_of_le_of_lt (Nat.le_max_left _ _) hk) θ wC wD wTs wTp wL _).1 hθ)
    ((h₂ k (lt_of_le_of_lt (Nat.le_max_right _ _) hk) θ wC wD wTs wTp wL _).1 hθ)

/-! ## The α-flip: defect-regime self-plays -/

theorem outcome_TauDupoc_vs_TauDupoc_highθ :
    ∃ k₂, ∀ k, k₂ < k → ∀ θ wC wD wTs wTp wL, wC + wTs + wTp + wL < θ →
      ∃ N, outcome N (TauDupoc k θ wC wD wTs wTp wL) (TauDupoc k θ wC wD wTs wTp wL)
        = some (.D, .D) := by
  obtain ⟨k₂, h⟩ := tauDupoc_phase
  exact ⟨k₂, fun k hk θ wC wD wTs wTp wL hθ =>
    outcome_of_ex_plays ((h k hk θ wC wD wTs wTp wL _).2 hθ)
      ((h k hk θ wC wD wTs wTp wL _).2 hθ)⟩

theorem outcome_TauTFTSim_vs_TauTFTSim_highθ :
    ∃ k₂, ∀ k, k₂ < k → ∀ θ wC wD wTs wTp wL, wC + wTs + wTp + wL < θ →
      ∃ N, outcome N (TauTFTSim k θ wC wD wTs wTp wL) (TauTFTSim k θ wC wD wTs wTp wL)
        = some (.D, .D) := by
  obtain ⟨k₂, h⟩ := tauTFTSim_phase
  exact ⟨k₂, fun k hk θ wC wD wTs wTp wL hθ =>
    outcome_of_ex_plays ((h k hk θ wC wD wTs wTp wL _).2 hθ)
      ((h k hk θ wC wD wTs wTp wL _).2 hθ)⟩

theorem outcome_TauTFTPf_vs_TauTFTPf_highθ :
    ∃ k₂, ∀ k, k₂ < k → ∀ θ wC wD wTs wTp wL, wC + wTs + wTp + wL < θ →
      ∃ N, outcome N (TauTFTPf k θ wC wD wTs wTp wL) (TauTFTPf k θ wC wD wTs wTp wL)
        = some (.D, .D) := by
  obtain ⟨k₂, h⟩ := tauTFTPf_phase
  exact ⟨k₂, fun k hk θ wC wD wTs wTp wL hθ =>
    outcome_of_ex_plays ((h k hk θ wC wD wTs wTp wL _).2 hθ)
      ((h k hk θ wC wD wTs wTp wL _).2 hθ)⟩

/-! ## The defect regime for the remaining cells

The α-flip completed off the diagonal. `Phases.lean` proves both directions for
every θ-bot (the phase theorems return a conjunction), so these are the `.2`
twins of the cooperative cells above. Note the pairs are NOT uniformly `(D, D)`:
constants never flip, so a mixed cell has exactly one flipping side — e.g.
`TauDupoc vs TauCooperate` is `(D, C)` here. -/

theorem outcome_TauDupoc_vs_TauCooperate_highθ :
    ∃ k₂, ∀ k, k₂ < k → ∀ θ wC wD wTs wTp wL, wC + wTs + wTp + wL < θ →
      ∃ N, outcome N (TauDupoc k θ wC wD wTs wTp wL) TauCooperate
        = some (.D, .C) := by
  obtain ⟨k₂, h⟩ := tauDupoc_phase
  exact ⟨k₂, fun k hk θ wC wD wTs wTp wL hθ =>
    outcome_of_ex_plays ((h k hk θ wC wD wTs wTp wL _).2 hθ) (tauCooperate_plays _)⟩

theorem outcome_TauDupoc_vs_TauDefect_highθ :
    ∃ k₂, ∀ k, k₂ < k → ∀ θ wC wD wTs wTp wL, wC + wTs + wTp + wL < θ →
      ∃ N, outcome N (TauDupoc k θ wC wD wTs wTp wL) TauDefect
        = some (.D, .D) := by
  obtain ⟨k₂, h⟩ := tauDupoc_phase
  exact ⟨k₂, fun k hk θ wC wD wTs wTp wL hθ =>
    outcome_of_ex_plays ((h k hk θ wC wD wTs wTp wL _).2 hθ) (tauDefect_plays _)⟩

theorem outcome_TauDupoc_vs_TauTFTSim_highθ :
    ∃ k₂, ∀ k, k₂ < k → ∀ θ wC wD wTs wTp wL, wC + wTs + wTp + wL < θ →
      ∃ N, outcome N (TauDupoc k θ wC wD wTs wTp wL) (TauTFTSim k θ wC wD wTs wTp wL)
        = some (.D, .D) := by
  obtain ⟨k₁, h₁⟩ := tauDupoc_phase
  obtain ⟨k₂, h₂⟩ := tauTFTSim_phase
  refine ⟨max k₁ k₂, fun k hk θ wC wD wTs wTp wL hθ => ?_⟩
  exact outcome_of_ex_plays
    ((h₁ k (lt_of_le_of_lt (Nat.le_max_left _ _) hk) θ wC wD wTs wTp wL _).2 hθ)
    ((h₂ k (lt_of_le_of_lt (Nat.le_max_right _ _) hk) θ wC wD wTs wTp wL _).2 hθ)

theorem outcome_TauDupoc_vs_TauTFTPf_highθ :
    ∃ k₂, ∀ k, k₂ < k → ∀ θ wC wD wTs wTp wL, wC + wTs + wTp + wL < θ →
      ∃ N, outcome N (TauDupoc k θ wC wD wTs wTp wL) (TauTFTPf k θ wC wD wTs wTp wL)
        = some (.D, .D) := by
  obtain ⟨k₁, h₁⟩ := tauDupoc_phase
  obtain ⟨k₂, h₂⟩ := tauTFTPf_phase
  refine ⟨max k₁ k₂, fun k hk θ wC wD wTs wTp wL hθ => ?_⟩
  exact outcome_of_ex_plays
    ((h₁ k (lt_of_le_of_lt (Nat.le_max_left _ _) hk) θ wC wD wTs wTp wL _).2 hθ)
    ((h₂ k (lt_of_le_of_lt (Nat.le_max_right _ _) hk) θ wC wD wTs wTp wL _).2 hθ)

theorem outcome_TauCooperate_vs_TauDupoc_highθ :
    ∃ k₂, ∀ k, k₂ < k → ∀ θ wC wD wTs wTp wL, wC + wTs + wTp + wL < θ →
      ∃ N, outcome N TauCooperate (TauDupoc k θ wC wD wTs wTp wL)
        = some (.C, .D) := by
  obtain ⟨k₂, h⟩ := tauDupoc_phase
  exact ⟨k₂, fun k hk θ wC wD wTs wTp wL hθ =>
    outcome_of_ex_plays (tauCooperate_plays _) ((h k hk θ wC wD wTs wTp wL _).2 hθ)⟩

theorem outcome_TauCooperate_vs_TauTFTSim_highθ :
    ∃ k₂, ∀ k, k₂ < k → ∀ θ wC wD wTs wTp wL, wC + wTs + wTp + wL < θ →
      ∃ N, outcome N TauCooperate (TauTFTSim k θ wC wD wTs wTp wL)
        = some (.C, .D) := by
  obtain ⟨k₂, h⟩ := tauTFTSim_phase
  exact ⟨k₂, fun k hk θ wC wD wTs wTp wL hθ =>
    outcome_of_ex_plays (tauCooperate_plays _) ((h k hk θ wC wD wTs wTp wL _).2 hθ)⟩

theorem outcome_TauCooperate_vs_TauTFTPf_highθ :
    ∃ k₂, ∀ k, k₂ < k → ∀ θ wC wD wTs wTp wL, wC + wTs + wTp + wL < θ →
      ∃ N, outcome N TauCooperate (TauTFTPf k θ wC wD wTs wTp wL)
        = some (.C, .D) := by
  obtain ⟨k₂, h⟩ := tauTFTPf_phase
  exact ⟨k₂, fun k hk θ wC wD wTs wTp wL hθ =>
    outcome_of_ex_plays (tauCooperate_plays _) ((h k hk θ wC wD wTs wTp wL _).2 hθ)⟩

theorem outcome_TauDefect_vs_TauDupoc_highθ :
    ∃ k₂, ∀ k, k₂ < k → ∀ θ wC wD wTs wTp wL, wC + wTs + wTp + wL < θ →
      ∃ N, outcome N TauDefect (TauDupoc k θ wC wD wTs wTp wL)
        = some (.D, .D) := by
  obtain ⟨k₂, h⟩ := tauDupoc_phase
  exact ⟨k₂, fun k hk θ wC wD wTs wTp wL hθ =>
    outcome_of_ex_plays (tauDefect_plays _) ((h k hk θ wC wD wTs wTp wL _).2 hθ)⟩

theorem outcome_TauDefect_vs_TauTFTSim_highθ :
    ∃ k₂, ∀ k, k₂ < k → ∀ θ wC wD wTs wTp wL, wC + wTs + wTp + wL < θ →
      ∃ N, outcome N TauDefect (TauTFTSim k θ wC wD wTs wTp wL)
        = some (.D, .D) := by
  obtain ⟨k₂, h⟩ := tauTFTSim_phase
  exact ⟨k₂, fun k hk θ wC wD wTs wTp wL hθ =>
    outcome_of_ex_plays (tauDefect_plays _) ((h k hk θ wC wD wTs wTp wL _).2 hθ)⟩

theorem outcome_TauDefect_vs_TauTFTPf_highθ :
    ∃ k₂, ∀ k, k₂ < k → ∀ θ wC wD wTs wTp wL, wC + wTs + wTp + wL < θ →
      ∃ N, outcome N TauDefect (TauTFTPf k θ wC wD wTs wTp wL)
        = some (.D, .D) := by
  obtain ⟨k₂, h⟩ := tauTFTPf_phase
  exact ⟨k₂, fun k hk θ wC wD wTs wTp wL hθ =>
    outcome_of_ex_plays (tauDefect_plays _) ((h k hk θ wC wD wTs wTp wL _).2 hθ)⟩

theorem outcome_TauTFTSim_vs_TauDupoc_highθ :
    ∃ k₂, ∀ k, k₂ < k → ∀ θ wC wD wTs wTp wL, wC + wTs + wTp + wL < θ →
      ∃ N, outcome N (TauTFTSim k θ wC wD wTs wTp wL) (TauDupoc k θ wC wD wTs wTp wL)
        = some (.D, .D) := by
  obtain ⟨k₁, h₁⟩ := tauTFTSim_phase
  obtain ⟨k₂, h₂⟩ := tauDupoc_phase
  refine ⟨max k₁ k₂, fun k hk θ wC wD wTs wTp wL hθ => ?_⟩
  exact outcome_of_ex_plays
    ((h₁ k (lt_of_le_of_lt (Nat.le_max_left _ _) hk) θ wC wD wTs wTp wL _).2 hθ)
    ((h₂ k (lt_of_le_of_lt (Nat.le_max_right _ _) hk) θ wC wD wTs wTp wL _).2 hθ)

theorem outcome_TauTFTSim_vs_TauCooperate_highθ :
    ∃ k₂, ∀ k, k₂ < k → ∀ θ wC wD wTs wTp wL, wC + wTs + wTp + wL < θ →
      ∃ N, outcome N (TauTFTSim k θ wC wD wTs wTp wL) TauCooperate
        = some (.D, .C) := by
  obtain ⟨k₂, h⟩ := tauTFTSim_phase
  exact ⟨k₂, fun k hk θ wC wD wTs wTp wL hθ =>
    outcome_of_ex_plays ((h k hk θ wC wD wTs wTp wL _).2 hθ) (tauCooperate_plays _)⟩

theorem outcome_TauTFTSim_vs_TauDefect_highθ :
    ∃ k₂, ∀ k, k₂ < k → ∀ θ wC wD wTs wTp wL, wC + wTs + wTp + wL < θ →
      ∃ N, outcome N (TauTFTSim k θ wC wD wTs wTp wL) TauDefect
        = some (.D, .D) := by
  obtain ⟨k₂, h⟩ := tauTFTSim_phase
  exact ⟨k₂, fun k hk θ wC wD wTs wTp wL hθ =>
    outcome_of_ex_plays ((h k hk θ wC wD wTs wTp wL _).2 hθ) (tauDefect_plays _)⟩

theorem outcome_TauTFTSim_vs_TauTFTPf_highθ :
    ∃ k₂, ∀ k, k₂ < k → ∀ θ wC wD wTs wTp wL, wC + wTs + wTp + wL < θ →
      ∃ N, outcome N (TauTFTSim k θ wC wD wTs wTp wL) (TauTFTPf k θ wC wD wTs wTp wL)
        = some (.D, .D) := by
  obtain ⟨k₁, h₁⟩ := tauTFTSim_phase
  obtain ⟨k₂, h₂⟩ := tauTFTPf_phase
  refine ⟨max k₁ k₂, fun k hk θ wC wD wTs wTp wL hθ => ?_⟩
  exact outcome_of_ex_plays
    ((h₁ k (lt_of_le_of_lt (Nat.le_max_left _ _) hk) θ wC wD wTs wTp wL _).2 hθ)
    ((h₂ k (lt_of_le_of_lt (Nat.le_max_right _ _) hk) θ wC wD wTs wTp wL _).2 hθ)

theorem outcome_TauTFTPf_vs_TauDupoc_highθ :
    ∃ k₂, ∀ k, k₂ < k → ∀ θ wC wD wTs wTp wL, wC + wTs + wTp + wL < θ →
      ∃ N, outcome N (TauTFTPf k θ wC wD wTs wTp wL) (TauDupoc k θ wC wD wTs wTp wL)
        = some (.D, .D) := by
  obtain ⟨k₁, h₁⟩ := tauTFTPf_phase
  obtain ⟨k₂, h₂⟩ := tauDupoc_phase
  refine ⟨max k₁ k₂, fun k hk θ wC wD wTs wTp wL hθ => ?_⟩
  exact outcome_of_ex_plays
    ((h₁ k (lt_of_le_of_lt (Nat.le_max_left _ _) hk) θ wC wD wTs wTp wL _).2 hθ)
    ((h₂ k (lt_of_le_of_lt (Nat.le_max_right _ _) hk) θ wC wD wTs wTp wL _).2 hθ)

theorem outcome_TauTFTPf_vs_TauCooperate_highθ :
    ∃ k₂, ∀ k, k₂ < k → ∀ θ wC wD wTs wTp wL, wC + wTs + wTp + wL < θ →
      ∃ N, outcome N (TauTFTPf k θ wC wD wTs wTp wL) TauCooperate
        = some (.D, .C) := by
  obtain ⟨k₂, h⟩ := tauTFTPf_phase
  exact ⟨k₂, fun k hk θ wC wD wTs wTp wL hθ =>
    outcome_of_ex_plays ((h k hk θ wC wD wTs wTp wL _).2 hθ) (tauCooperate_plays _)⟩

theorem outcome_TauTFTPf_vs_TauDefect_highθ :
    ∃ k₂, ∀ k, k₂ < k → ∀ θ wC wD wTs wTp wL, wC + wTs + wTp + wL < θ →
      ∃ N, outcome N (TauTFTPf k θ wC wD wTs wTp wL) TauDefect
        = some (.D, .D) := by
  obtain ⟨k₂, h⟩ := tauTFTPf_phase
  exact ⟨k₂, fun k hk θ wC wD wTs wTp wL hθ =>
    outcome_of_ex_plays ((h k hk θ wC wD wTs wTp wL _).2 hθ) (tauDefect_plays _)⟩

theorem outcome_TauTFTPf_vs_TauTFTSim_highθ :
    ∃ k₂, ∀ k, k₂ < k → ∀ θ wC wD wTs wTp wL, wC + wTs + wTp + wL < θ →
      ∃ N, outcome N (TauTFTPf k θ wC wD wTs wTp wL) (TauTFTSim k θ wC wD wTs wTp wL)
        = some (.D, .D) := by
  obtain ⟨k₁, h₁⟩ := tauTFTPf_phase
  obtain ⟨k₂, h₂⟩ := tauTFTSim_phase
  refine ⟨max k₁ k₂, fun k hk θ wC wD wTs wTp wL hθ => ?_⟩
  exact outcome_of_ex_plays
    ((h₁ k (lt_of_le_of_lt (Nat.le_max_left _ _) hk) θ wC wD wTs wTp wL _).2 hθ)
    ((h₂ k (lt_of_le_of_lt (Nat.le_max_right _ _) hk) θ wC wD wTs wTp wL _).2 hθ)


/-! ## TauEBot cells — the SEPARATING bot

`TauEBot` is what makes Def 3 and Def 4 actually differ: base `EBot vs
DupocBot` is `(C, D)` — ASYMMETRIC and under conditional bots — so the
self-probe and reciprocity-probe read different bits for it, shifting the
α-boundary. See `Tau/Defs.lean`.

Mixed pairs bind BOTH weight vectors (`wL` for the δ_L-column bots, `wE` for
TauEBot) and take a CONJUNCTION of the two regime hypotheses, because the two
bots threshold against different masses — there is no single shared boundary
once the zoo contains bots probing different columns. -/

theorem outcome_TauEBot_vs_TauCooperate :
    ∃ k₂, ∀ k, k₂ < k → ∀ θ wC wD wTs wTp wE, θ ≤ wC + wE →
      ∃ N, outcome N (TauEBot k θ wC wD wTs wTp wE) TauCooperate
        = some (.C, .C) := by
  obtain ⟨k₂, h⟩ := tauEBot_phase
  exact ⟨k₂, fun k hk θ wC wD wTs wTp wE hθ =>
    outcome_of_ex_plays ((h k hk θ wC wD wTs wTp wE _).1 hθ) (tauCooperate_plays _)⟩

theorem outcome_TauEBot_vs_TauDefect :
    ∃ k₂, ∀ k, k₂ < k → ∀ θ wC wD wTs wTp wE, θ ≤ wC + wE →
      ∃ N, outcome N (TauEBot k θ wC wD wTs wTp wE) TauDefect
        = some (.C, .D) := by
  obtain ⟨k₂, h⟩ := tauEBot_phase
  exact ⟨k₂, fun k hk θ wC wD wTs wTp wE hθ =>
    outcome_of_ex_plays ((h k hk θ wC wD wTs wTp wE _).1 hθ) (tauDefect_plays _)⟩

theorem outcome_TauEBot_vs_TauDupoc :
    ∃ k₂, ∀ k, k₂ < k → ∀ θ wC wD wTs wTp wL wE, θ ≤ wC + wE → θ ≤ wC + wTs + wTp + wL →
      ∃ N, outcome N (TauEBot k θ wC wD wTs wTp wE) (TauDupoc k θ wC wD wTs wTp wL)
        = some (.C, .C) := by
  obtain ⟨k₁, h₁⟩ := tauEBot_phase
  obtain ⟨k₂, h₂⟩ := tauDupoc_phase
  refine ⟨max k₁ k₂, fun k hk θ wC wD wTs wTp wL wE hθ₁ hθ₂ => ?_⟩
  exact outcome_of_ex_plays
    ((h₁ k (lt_of_le_of_lt (Nat.le_max_left _ _) hk) θ wC wD wTs wTp wE _).1 hθ₁)
    ((h₂ k (lt_of_le_of_lt (Nat.le_max_right _ _) hk) θ wC wD wTs wTp wL _).1 hθ₂)

theorem outcome_TauEBot_vs_TauTFTSim :
    ∃ k₂, ∀ k, k₂ < k → ∀ θ wC wD wTs wTp wL wE, θ ≤ wC + wE → θ ≤ wC + wTs + wTp + wL →
      ∃ N, outcome N (TauEBot k θ wC wD wTs wTp wE) (TauTFTSim k θ wC wD wTs wTp wL)
        = some (.C, .C) := by
  obtain ⟨k₁, h₁⟩ := tauEBot_phase
  obtain ⟨k₂, h₂⟩ := tauTFTSim_phase
  refine ⟨max k₁ k₂, fun k hk θ wC wD wTs wTp wL wE hθ₁ hθ₂ => ?_⟩
  exact outcome_of_ex_plays
    ((h₁ k (lt_of_le_of_lt (Nat.le_max_left _ _) hk) θ wC wD wTs wTp wE _).1 hθ₁)
    ((h₂ k (lt_of_le_of_lt (Nat.le_max_right _ _) hk) θ wC wD wTs wTp wL _).1 hθ₂)

theorem outcome_TauEBot_vs_TauTFTPf :
    ∃ k₂, ∀ k, k₂ < k → ∀ θ wC wD wTs wTp wL wE, θ ≤ wC + wE → θ ≤ wC + wTs + wTp + wL →
      ∃ N, outcome N (TauEBot k θ wC wD wTs wTp wE) (TauTFTPf k θ wC wD wTs wTp wL)
        = some (.C, .C) := by
  obtain ⟨k₁, h₁⟩ := tauEBot_phase
  obtain ⟨k₂, h₂⟩ := tauTFTPf_phase
  refine ⟨max k₁ k₂, fun k hk θ wC wD wTs wTp wL wE hθ₁ hθ₂ => ?_⟩
  exact outcome_of_ex_plays
    ((h₁ k (lt_of_le_of_lt (Nat.le_max_left _ _) hk) θ wC wD wTs wTp wE _).1 hθ₁)
    ((h₂ k (lt_of_le_of_lt (Nat.le_max_right _ _) hk) θ wC wD wTs wTp wL _).1 hθ₂)

theorem outcome_TauEBot_vs_TauEBot :
    ∃ k₂, ∀ k, k₂ < k → ∀ θ wC wD wTs wTp wE, θ ≤ wC + wE →
      ∃ N, outcome N (TauEBot k θ wC wD wTs wTp wE) (TauEBot k θ wC wD wTs wTp wE)
        = some (.C, .C) := by
  obtain ⟨k₂, h⟩ := tauEBot_phase
  exact ⟨k₂, fun k hk θ wC wD wTs wTp wE hθ =>
    outcome_of_ex_plays ((h k hk θ wC wD wTs wTp wE _).1 hθ)
      ((h k hk θ wC wD wTs wTp wE _).1 hθ)⟩

theorem outcome_TauCooperate_vs_TauEBot :
    ∃ k₂, ∀ k, k₂ < k → ∀ θ wC wD wTs wTp wE, θ ≤ wC + wE →
      ∃ N, outcome N TauCooperate (TauEBot k θ wC wD wTs wTp wE)
        = some (.C, .C) := by
  obtain ⟨k₂, h⟩ := tauEBot_phase
  exact ⟨k₂, fun k hk θ wC wD wTs wTp wE hθ =>
    outcome_of_ex_plays (tauCooperate_plays _) ((h k hk θ wC wD wTs wTp wE _).1 hθ)⟩

theorem outcome_TauDefect_vs_TauEBot :
    ∃ k₂, ∀ k, k₂ < k → ∀ θ wC wD wTs wTp wE, θ ≤ wC + wE →
      ∃ N, outcome N TauDefect (TauEBot k θ wC wD wTs wTp wE)
        = some (.D, .C) := by
  obtain ⟨k₂, h⟩ := tauEBot_phase
  exact ⟨k₂, fun k hk θ wC wD wTs wTp wE hθ =>
    outcome_of_ex_plays (tauDefect_plays _) ((h k hk θ wC wD wTs wTp wE _).1 hθ)⟩

theorem outcome_TauDupoc_vs_TauEBot :
    ∃ k₂, ∀ k, k₂ < k → ∀ θ wC wD wTs wTp wL wE, θ ≤ wC + wE → θ ≤ wC + wTs + wTp + wL →
      ∃ N, outcome N (TauDupoc k θ wC wD wTs wTp wL) (TauEBot k θ wC wD wTs wTp wE)
        = some (.C, .C) := by
  obtain ⟨k₁, h₁⟩ := tauDupoc_phase
  obtain ⟨k₂, h₂⟩ := tauEBot_phase
  refine ⟨max k₁ k₂, fun k hk θ wC wD wTs wTp wL wE hθ₁ hθ₂ => ?_⟩
  exact outcome_of_ex_plays
    ((h₁ k (lt_of_le_of_lt (Nat.le_max_left _ _) hk) θ wC wD wTs wTp wL _).1 hθ₂)
    ((h₂ k (lt_of_le_of_lt (Nat.le_max_right _ _) hk) θ wC wD wTs wTp wE _).1 hθ₁)

theorem outcome_TauTFTSim_vs_TauEBot :
    ∃ k₂, ∀ k, k₂ < k → ∀ θ wC wD wTs wTp wL wE, θ ≤ wC + wE → θ ≤ wC + wTs + wTp + wL →
      ∃ N, outcome N (TauTFTSim k θ wC wD wTs wTp wL) (TauEBot k θ wC wD wTs wTp wE)
        = some (.C, .C) := by
  obtain ⟨k₁, h₁⟩ := tauTFTSim_phase
  obtain ⟨k₂, h₂⟩ := tauEBot_phase
  refine ⟨max k₁ k₂, fun k hk θ wC wD wTs wTp wL wE hθ₁ hθ₂ => ?_⟩
  exact outcome_of_ex_plays
    ((h₁ k (lt_of_le_of_lt (Nat.le_max_left _ _) hk) θ wC wD wTs wTp wL _).1 hθ₂)
    ((h₂ k (lt_of_le_of_lt (Nat.le_max_right _ _) hk) θ wC wD wTs wTp wE _).1 hθ₁)

theorem outcome_TauTFTPf_vs_TauEBot :
    ∃ k₂, ∀ k, k₂ < k → ∀ θ wC wD wTs wTp wL wE, θ ≤ wC + wE → θ ≤ wC + wTs + wTp + wL →
      ∃ N, outcome N (TauTFTPf k θ wC wD wTs wTp wL) (TauEBot k θ wC wD wTs wTp wE)
        = some (.C, .C) := by
  obtain ⟨k₁, h₁⟩ := tauTFTPf_phase
  obtain ⟨k₂, h₂⟩ := tauEBot_phase
  refine ⟨max k₁ k₂, fun k hk θ wC wD wTs wTp wL wE hθ₁ hθ₂ => ?_⟩
  exact outcome_of_ex_plays
    ((h₁ k (lt_of_le_of_lt (Nat.le_max_left _ _) hk) θ wC wD wTs wTp wL _).1 hθ₂)
    ((h₂ k (lt_of_le_of_lt (Nat.le_max_right _ _) hk) θ wC wD wTs wTp wE _).1 hθ₁)

theorem outcome_TauEBot_vs_TauCooperate_highθ :
    ∃ k₂, ∀ k, k₂ < k → ∀ θ wC wD wTs wTp wE, wC + wE < θ →
      ∃ N, outcome N (TauEBot k θ wC wD wTs wTp wE) TauCooperate
        = some (.D, .C) := by
  obtain ⟨k₂, h⟩ := tauEBot_phase
  exact ⟨k₂, fun k hk θ wC wD wTs wTp wE hθ =>
    outcome_of_ex_plays ((h k hk θ wC wD wTs wTp wE _).2 hθ) (tauCooperate_plays _)⟩

theorem outcome_TauEBot_vs_TauDefect_highθ :
    ∃ k₂, ∀ k, k₂ < k → ∀ θ wC wD wTs wTp wE, wC + wE < θ →
      ∃ N, outcome N (TauEBot k θ wC wD wTs wTp wE) TauDefect
        = some (.D, .D) := by
  obtain ⟨k₂, h⟩ := tauEBot_phase
  exact ⟨k₂, fun k hk θ wC wD wTs wTp wE hθ =>
    outcome_of_ex_plays ((h k hk θ wC wD wTs wTp wE _).2 hθ) (tauDefect_plays _)⟩

theorem outcome_TauEBot_vs_TauDupoc_highθ :
    ∃ k₂, ∀ k, k₂ < k → ∀ θ wC wD wTs wTp wL wE, wC + wE < θ → wC + wTs + wTp + wL < θ →
      ∃ N, outcome N (TauEBot k θ wC wD wTs wTp wE) (TauDupoc k θ wC wD wTs wTp wL)
        = some (.D, .D) := by
  obtain ⟨k₁, h₁⟩ := tauEBot_phase
  obtain ⟨k₂, h₂⟩ := tauDupoc_phase
  refine ⟨max k₁ k₂, fun k hk θ wC wD wTs wTp wL wE hθ₁ hθ₂ => ?_⟩
  exact outcome_of_ex_plays
    ((h₁ k (lt_of_le_of_lt (Nat.le_max_left _ _) hk) θ wC wD wTs wTp wE _).2 hθ₁)
    ((h₂ k (lt_of_le_of_lt (Nat.le_max_right _ _) hk) θ wC wD wTs wTp wL _).2 hθ₂)

theorem outcome_TauEBot_vs_TauTFTSim_highθ :
    ∃ k₂, ∀ k, k₂ < k → ∀ θ wC wD wTs wTp wL wE, wC + wE < θ → wC + wTs + wTp + wL < θ →
      ∃ N, outcome N (TauEBot k θ wC wD wTs wTp wE) (TauTFTSim k θ wC wD wTs wTp wL)
        = some (.D, .D) := by
  obtain ⟨k₁, h₁⟩ := tauEBot_phase
  obtain ⟨k₂, h₂⟩ := tauTFTSim_phase
  refine ⟨max k₁ k₂, fun k hk θ wC wD wTs wTp wL wE hθ₁ hθ₂ => ?_⟩
  exact outcome_of_ex_plays
    ((h₁ k (lt_of_le_of_lt (Nat.le_max_left _ _) hk) θ wC wD wTs wTp wE _).2 hθ₁)
    ((h₂ k (lt_of_le_of_lt (Nat.le_max_right _ _) hk) θ wC wD wTs wTp wL _).2 hθ₂)

theorem outcome_TauEBot_vs_TauTFTPf_highθ :
    ∃ k₂, ∀ k, k₂ < k → ∀ θ wC wD wTs wTp wL wE, wC + wE < θ → wC + wTs + wTp + wL < θ →
      ∃ N, outcome N (TauEBot k θ wC wD wTs wTp wE) (TauTFTPf k θ wC wD wTs wTp wL)
        = some (.D, .D) := by
  obtain ⟨k₁, h₁⟩ := tauEBot_phase
  obtain ⟨k₂, h₂⟩ := tauTFTPf_phase
  refine ⟨max k₁ k₂, fun k hk θ wC wD wTs wTp wL wE hθ₁ hθ₂ => ?_⟩
  exact outcome_of_ex_plays
    ((h₁ k (lt_of_le_of_lt (Nat.le_max_left _ _) hk) θ wC wD wTs wTp wE _).2 hθ₁)
    ((h₂ k (lt_of_le_of_lt (Nat.le_max_right _ _) hk) θ wC wD wTs wTp wL _).2 hθ₂)

theorem outcome_TauEBot_vs_TauEBot_highθ :
    ∃ k₂, ∀ k, k₂ < k → ∀ θ wC wD wTs wTp wE, wC + wE < θ →
      ∃ N, outcome N (TauEBot k θ wC wD wTs wTp wE) (TauEBot k θ wC wD wTs wTp wE)
        = some (.D, .D) := by
  obtain ⟨k₂, h⟩ := tauEBot_phase
  exact ⟨k₂, fun k hk θ wC wD wTs wTp wE hθ =>
    outcome_of_ex_plays ((h k hk θ wC wD wTs wTp wE _).2 hθ)
      ((h k hk θ wC wD wTs wTp wE _).2 hθ)⟩

theorem outcome_TauCooperate_vs_TauEBot_highθ :
    ∃ k₂, ∀ k, k₂ < k → ∀ θ wC wD wTs wTp wE, wC + wE < θ →
      ∃ N, outcome N TauCooperate (TauEBot k θ wC wD wTs wTp wE)
        = some (.C, .D) := by
  obtain ⟨k₂, h⟩ := tauEBot_phase
  exact ⟨k₂, fun k hk θ wC wD wTs wTp wE hθ =>
    outcome_of_ex_plays (tauCooperate_plays _) ((h k hk θ wC wD wTs wTp wE _).2 hθ)⟩

theorem outcome_TauDefect_vs_TauEBot_highθ :
    ∃ k₂, ∀ k, k₂ < k → ∀ θ wC wD wTs wTp wE, wC + wE < θ →
      ∃ N, outcome N TauDefect (TauEBot k θ wC wD wTs wTp wE)
        = some (.D, .D) := by
  obtain ⟨k₂, h⟩ := tauEBot_phase
  exact ⟨k₂, fun k hk θ wC wD wTs wTp wE hθ =>
    outcome_of_ex_plays (tauDefect_plays _) ((h k hk θ wC wD wTs wTp wE _).2 hθ)⟩

theorem outcome_TauDupoc_vs_TauEBot_highθ :
    ∃ k₂, ∀ k, k₂ < k → ∀ θ wC wD wTs wTp wL wE, wC + wE < θ → wC + wTs + wTp + wL < θ →
      ∃ N, outcome N (TauDupoc k θ wC wD wTs wTp wL) (TauEBot k θ wC wD wTs wTp wE)
        = some (.D, .D) := by
  obtain ⟨k₁, h₁⟩ := tauDupoc_phase
  obtain ⟨k₂, h₂⟩ := tauEBot_phase
  refine ⟨max k₁ k₂, fun k hk θ wC wD wTs wTp wL wE hθ₁ hθ₂ => ?_⟩
  exact outcome_of_ex_plays
    ((h₁ k (lt_of_le_of_lt (Nat.le_max_left _ _) hk) θ wC wD wTs wTp wL _).2 hθ₂)
    ((h₂ k (lt_of_le_of_lt (Nat.le_max_right _ _) hk) θ wC wD wTs wTp wE _).2 hθ₁)

theorem outcome_TauTFTSim_vs_TauEBot_highθ :
    ∃ k₂, ∀ k, k₂ < k → ∀ θ wC wD wTs wTp wL wE, wC + wE < θ → wC + wTs + wTp + wL < θ →
      ∃ N, outcome N (TauTFTSim k θ wC wD wTs wTp wL) (TauEBot k θ wC wD wTs wTp wE)
        = some (.D, .D) := by
  obtain ⟨k₁, h₁⟩ := tauTFTSim_phase
  obtain ⟨k₂, h₂⟩ := tauEBot_phase
  refine ⟨max k₁ k₂, fun k hk θ wC wD wTs wTp wL wE hθ₁ hθ₂ => ?_⟩
  exact outcome_of_ex_plays
    ((h₁ k (lt_of_le_of_lt (Nat.le_max_left _ _) hk) θ wC wD wTs wTp wL _).2 hθ₂)
    ((h₂ k (lt_of_le_of_lt (Nat.le_max_right _ _) hk) θ wC wD wTs wTp wE _).2 hθ₁)

theorem outcome_TauTFTPf_vs_TauEBot_highθ :
    ∃ k₂, ∀ k, k₂ < k → ∀ θ wC wD wTs wTp wL wE, wC + wE < θ → wC + wTs + wTp + wL < θ →
      ∃ N, outcome N (TauTFTPf k θ wC wD wTs wTp wL) (TauEBot k θ wC wD wTs wTp wE)
        = some (.D, .D) := by
  obtain ⟨k₁, h₁⟩ := tauTFTPf_phase
  obtain ⟨k₂, h₂⟩ := tauEBot_phase
  refine ⟨max k₁ k₂, fun k hk θ wC wD wTs wTp wL wE hθ₁ hθ₂ => ?_⟩
  exact outcome_of_ex_plays
    ((h₁ k (lt_of_le_of_lt (Nat.le_max_left _ _) hk) θ wC wD wTs wTp wL _).2 hθ₂)
    ((h₂ k (lt_of_le_of_lt (Nat.le_max_right _ _) hk) θ wC wD wTs wTp wE _).2 hθ₁)

end PD.Theorems.Tau
