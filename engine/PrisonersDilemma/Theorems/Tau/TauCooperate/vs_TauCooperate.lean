import PrisonersDilemma.Tau.VotePhases

/-!
# τ(Coop) self-play.

Per-pair layout (the base-zoo convention): every cell is a corollary of the α-phase
theorems in `Tau/VotePhases.lean` — tau players are `.opp`-free, hence extensionally
constant, so a match is two independent plays glued by `outcome_of_ex_plays`.
Regime masses: `coopMass`/`eMass` (VotePhases).
-/

open PD PD.Tau PD.BaseTheorems

namespace PD.Theorems.Tau

theorem outcome_TauCooperate_vs_TauCooperate (k : Nat) (w : Tmpl → Nat) (θ : Nat)
    (hθ : θ ≤ w .coop + (w .defect + (w .tftSim + (w .tftPf + (w .dupoc + (w .ebot + 0)))))) :
    ∃ N, outcome N (TauBotZ k .coop w θ) (TauBotZ k .coop w θ) = some (.C, .C) :=
  outcome_of_ex_plays
    ((tauCooperate_phase k w θ _).1 hθ)
    ((tauCooperate_phase k w θ _).1 hθ)

end PD.Theorems.Tau
