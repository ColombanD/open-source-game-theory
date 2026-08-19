import PrisonersDilemma.Tau.VotePhases

/-!
# τ(Defect) vs τ(Coop) — the mirror exploitation cell.

Per-pair layout (the base-zoo convention): every cell is a corollary of the α-phase
theorems in `Tau/VotePhases.lean` — tau players are `.opp`-free, hence extensionally
constant, so a match is two independent plays glued by `outcome_of_ex_plays`.
Regime masses: `coopMass`/`eMass` (VotePhases).
-/

open PD PD.Tau PD.BaseTheorems

namespace PD.Theorems.Tau

theorem outcome_TauDefect_vs_TauCooperate (k : Nat) (w : Tmpl → Nat) (θ : Nat)
    (hθ : θ ≤ w .coop + (w .defect + (w .tftSim + (w .tftPf + (w .dupoc + (w .ebot + 0))))))
    (hθ0 : θ ≠ 0) :
    ∃ N, outcome N (TauBotZ k .defect w θ) (TauBotZ k .coop w θ) = some (.D, .C) :=
  outcome_of_ex_plays
    ((tauDefect_phase k w θ _).2 hθ0)
    ((tauCooperate_phase k w θ _).1 hθ)

end PD.Theorems.Tau
