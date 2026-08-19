import PrisonersDilemma.Tau.VotePhases

/-!
# τ(EBot) vs τ(TFTPf) — the band cell (mirror) and the shared cooperative
regime, where the exploiter reciprocates the prover TFT.

Per-pair layout (the base-zoo convention): every cell is a corollary of the α-phase
theorems in `Tau/VotePhases.lean` — tau players are `.opp`-free, hence extensionally
constant, so a match is two independent plays glued by `outcome_of_ex_plays`.
Regime masses: `coopMass`/`eMass` (VotePhases).
-/

open PD PD.Tau PD.BaseTheorems

namespace PD.Theorems.Tau

theorem outcome_TauEBot_vs_TauTFTPf_band {k : Nat} (hk : 2 ≤ k) (hkk : c_guard k + 3 ≤ k)
    (h6 : 6 ≤ k) (θ : Nat) (w : Tmpl → Nat)
    (hlo : ¬ θ ≤ eMass w) (hhi : θ ≤ coopMass w) :
    ∃ N, outcome N (TauBotZ k .ebot w θ) (TauBotZ k .tftPf w θ) = some (.D, .C) :=
  outcome_of_ex_plays
    ((tauEBot_phase hk hkk h6 θ w _).2 hlo)
    ((tauTFTPf_phase hk hkk h6 θ w _).1 hhi)

/-- Inside the shared cooperative regime the exploiter reciprocates the prover TFT. -/
theorem outcome_TauEBot_vs_TauTFTPf_coop {k : Nat} (hk : 2 ≤ k) (hkk : c_guard k + 3 ≤ k)
    (h6 : 6 ≤ k) (θ : Nat) (w : Tmpl → Nat) (hθ : θ ≤ eMass w) :
    ∃ N, outcome N (TauBotZ k .ebot w θ) (TauBotZ k .tftPf w θ) = some (.C, .C) :=
  outcome_of_ex_plays
    ((tauEBot_phase hk hkk h6 θ w _).1 hθ)
    ((tauTFTPf_phase hk hkk h6 θ w _).1 (by simp only [coopMass, eMass] at *; omega))

end PD.Theorems.Tau
