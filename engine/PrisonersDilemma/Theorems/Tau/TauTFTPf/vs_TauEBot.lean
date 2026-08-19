import PrisonersDilemma.Tau.VotePhases

/-!
# τ(TFTPf) vs τ(EBot) — THE SEPARATING BAND `eMass < θ ≤ coopMass` (nonempty
iff `w .coop > 0`): the cooperator still cooperates while the exploiter has
already flipped — the one-sided boundary made observable as a matrix cell.

Per-pair layout (the base-zoo convention): every cell is a corollary of the α-phase
theorems in `Tau/VotePhases.lean` — tau players are `.opp`-free, hence extensionally
constant, so a match is two independent plays glued by `outcome_of_ex_plays`.
Regime masses: `coopMass`/`eMass` (VotePhases).
-/

open PD PD.Tau PD.BaseTheorems

namespace PD.Theorems.Tau

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

end PD.Theorems.Tau
