import PrisonersDilemma.Tau.VotePhases

/-!
# τ(Dupoc) self-play — Löb-gated (`∃ k₂, ∀ k > k₂, …`): the quine entry needs
the bounded-Löb threshold.

Per-pair layout (the base-zoo convention): every cell is a corollary of the α-phase
theorems in `Tau/VotePhases.lean` — tau players are `.opp`-free, hence extensionally
constant, so a match is two independent plays glued by `outcome_of_ex_plays`.
Regime masses: `coopMass`/`eMass` (VotePhases).
-/

open PD PD.Tau PD.BaseTheorems

namespace PD.Theorems.Tau

theorem outcome_TauDupoc_vs_TauDupoc :
    ∃ k₂, ∀ k, k₂ < k → ∀ θ (w : Tmpl → Nat), θ ≤ coopMass w →
      ∃ N, outcome N (TauBotZ k .dupoc w θ) (TauBotZ k .dupoc w θ) = some (.C, .C) := by
  obtain ⟨k₂, h⟩ := tauDupoc_phase
  exact ⟨k₂, fun k hk θ w hθ =>
    outcome_of_ex_plays ((h k hk θ w _).1 hθ) ((h k hk θ w _).1 hθ)⟩

end PD.Theorems.Tau
