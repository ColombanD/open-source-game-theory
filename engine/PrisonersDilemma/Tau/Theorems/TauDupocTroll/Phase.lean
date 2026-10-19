import PrisonersDilemma.Tau.Theorems.Columns
import PrisonersDilemma.Tau.RowSpec
import PrisonersDilemma.Outcome.Attr

/-!
# τ(DupocTrollBot)'s phase — cooperates up to everything but Dupoc's source.

The twin of `TauCupodTroll/Phase.lean`: D at the hypotheses whose source is Dupoc's
(`.dupoc`, `.maxconfidence`, `.minconfidence` — the natives ARE Dupoc as hypotheses), C
everywhere else, so its boundary is `θ ≤ fullMass − (w .dupoc + w .maxconfidence + w .minconfidence)`.
-/

open PD PD.BaseTheorems

namespace PD.Tau

/-- τ(DupocTroll)'s bit ROW: D at the hypotheses it recognises, C elsewhere. -/
def dupocTrollRow : Tmpl → Action
  | .dupoc | .maxconfidence | .minconfidence => .D
  | _ => .C

theorem dupocTrollRow_plays {k : Nat} (hk : 3 ≤ k) :
    ∀ T, ∃ N, eval N (.bot (inst (tauZoo k) .dupocTroll T))
              (.bot (inst (tauZoo k) .dupocTroll T))
              (inst (tauZoo k) .dupocTroll T) = some (dupocTrollRow T)
  | .dupoc => dupocTroll_plays_D_at hk _ rfl
  | .maxconfidence => dupocTroll_plays_D_at hk _ rfl
  | .minconfidence => dupocTroll_plays_D_at hk _ rfl
  | .coop | .defect | .tftSim | .tftPf | .ebot | .just | .obot
  | .guardian | .dbot | .cupodTroll | .cupod | .cimcic | .dimcid | .prudent
  | .dupocTroll | .dimdid | .mirror =>
      dupocTroll_plays_C _ (by decide)

/-- **τ(DupocTroll)'s row** — the matrix-facing statement (`@[tau_row]`: validated by
    `Tau/Lint.lean`, exported to the app): unconditional at large `k`. -/
@[tau_row]
theorem dupocTrollRowSpec : RowSpec .dupocTroll tauOrder dupocTrollRow :=
  ⟨2, fun k hk T _ => dupocTrollRow_plays (by omega) T⟩

/-- **τ(DupocTrollBot)**: cooperates up to everything but the weight of the
    hypotheses it convicts. -/
theorem tauDupocTroll_phase {k : Nat} (hk : 3 ≤ k) (w : Tmpl → Nat) (θ : Nat)
    (opponent : Prog) :
    (θ ≤ bitMass w dupocTrollRow tauOrder →
      ∃ N, play N (TauBotZ k .dupocTroll w θ) opponent = some .C)
    ∧ (¬ θ ≤ bitMass w dupocTrollRow tauOrder →
      ∃ N, play N (TauBotZ k .dupocTroll w θ) opponent = some .D) :=
  phase_of_bits (tauZoo k) .dupocTroll w dupocTrollRow tauOrder θ opponent
    (fun T _ => dupocTrollRow_plays hk T)

end PD.Tau
