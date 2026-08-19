import PrisonersDilemma.Tau.VotePhases

/-!
# τ(EBot) self-play — BOTH regimes of the ONE-SIDED boundary (`θ ≤ eMass`).
No window: the retracted crowd-exploiter's window cells have no counterpart here.

Per-pair layout (the base-zoo convention): every cell is a corollary of the α-phase
theorems in `Tau/VotePhases.lean` — tau players are `.opp`-free, hence extensionally
constant, so a match is two independent plays glued by `outcome_of_ex_plays`.
Regime masses: `coopMass`/`eMass` (VotePhases).
-/

open PD PD.Tau PD.BaseTheorems

namespace PD.Theorems.Tau

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

end PD.Theorems.Tau
