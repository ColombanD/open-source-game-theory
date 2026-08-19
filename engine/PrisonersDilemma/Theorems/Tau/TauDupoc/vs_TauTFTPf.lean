import PrisonersDilemma.Tau.VotePhases

/-!
# τ(Dupoc) vs τ(TFTPf) — Löbian cooperator meets prover TFT.

Per-pair layout (the base-zoo convention): every cell is a corollary of the α-phase
theorems in `Tau/VotePhases.lean` — tau players are `.opp`-free, hence extensionally
constant, so a match is two independent plays glued by `outcome_of_ex_plays`.
Regime masses: `coopMass`/`eMass` (VotePhases).
-/

open PD PD.Tau PD.BaseTheorems

namespace PD.Theorems.Tau

theorem outcome_TauDupoc_vs_TauTFTPf :
    ∃ k₂, ∀ k, k₂ < k → 2 ≤ k → c_guard k + 3 ≤ k → 6 ≤ k →
      ∀ θ (w : Tmpl → Nat), θ ≤ coopMass w →
      ∃ N, outcome N (TauBotZ k .dupoc w θ) (TauBotZ k .tftPf w θ) = some (.C, .C) := by
  obtain ⟨k₂, h⟩ := tauDupoc_phase
  exact ⟨k₂, fun k hk hk2 hkk h6 θ w hθ =>
    outcome_of_ex_plays ((h k hk θ w _).1 hθ)
      ((tauTFTPf_phase hk2 hkk h6 θ w _).1 hθ)⟩

end PD.Theorems.Tau
