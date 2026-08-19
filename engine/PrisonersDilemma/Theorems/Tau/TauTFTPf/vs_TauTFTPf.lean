import PrisonersDilemma.Tau.VotePhases

/-!
# τ(TFTPf) self-play — the cooperative regime (`θ ≤ coopMass`).

Per-pair layout (the base-zoo convention): every cell is a corollary of the α-phase
theorems in `Tau/VotePhases.lean` — tau players are `.opp`-free, hence extensionally
constant, so a match is two independent plays glued by `outcome_of_ex_plays`.
Regime masses: `coopMass`/`eMass` (VotePhases).
-/

open PD PD.Tau PD.BaseTheorems

namespace PD.Theorems.Tau

theorem outcome_TauTFTPf_vs_TauTFTPf {k : Nat} (hk : 2 ≤ k) (hkk : c_guard k + 3 ≤ k)
    (h6 : 6 ≤ k) (θ : Nat) (w : Tmpl → Nat) (hθ : θ ≤ coopMass w) :
    ∃ N, outcome N (TauBotZ k .tftPf w θ) (TauBotZ k .tftPf w θ) = some (.C, .C) :=
  outcome_of_ex_plays
    ((tauTFTPf_phase hk hkk h6 θ w _).1 hθ)
    ((tauTFTPf_phase hk hkk h6 θ w _).1 hθ)

end PD.Theorems.Tau
