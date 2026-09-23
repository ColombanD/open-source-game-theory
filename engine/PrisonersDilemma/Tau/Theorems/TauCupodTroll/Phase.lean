import PrisonersDilemma.Tau.Theorems.Columns
import PrisonersDilemma.Tau.RowSpec
import PrisonersDilemma.Outcome.Attr

/-!
# τ(CupodTrollBot)'s phase — the full-mass cooperator (on THIS zoo).

Its identity check never fires, because the bot it looks for (CupodBot) is
`.sys`-blocked and therefore absent from the zoo. So every stage falls through and
the row is uniformly C: boundary `θ ≤ fullMass`, the same as τ(CooperateBot)'s.

**This is a faithful lift of a bot whose only target is missing**, not a degenerate
one — see `Helpers.lean`. The row will change the day CupodBot lands, which makes
this bot the zoo's standing regression test for the `.sys` milestone.
-/

open PD PD.BaseTheorems

namespace PD.Tau

/-- τ(CupodTroll)'s bit ROW: D at the ONE hypothesis it recognises, C elsewhere.
    (Was uniformly C until 2026-08-24, when `proveEq` was restated to ask about
    the HYPOTHESIS rather than `.opp` — the old guard could never fire.) -/
def cupodTrollRow : Tmpl → Action
  | .cupod => .D
  | _      => .C

theorem cupodTrollRow_plays {k : Nat} (hk : 3 ≤ k) :
    ∀ T, ∃ N, eval N (.bot (inst (tauZoo k) .cupodTroll T))
              (.bot (inst (tauZoo k) .cupodTroll T))
              (inst (tauZoo k) .cupodTroll T) = some (cupodTrollRow T)
  | .cupod => cupodTroll_plays_D_at_cupod hk
  | .coop | .defect | .tftSim | .tftPf | .dupoc | .ebot | .just | .obot
  | .guardian | .dbot | .cupodTroll | .cimcic | .dimcid | .prudent | .maxconfidence | .minconfidence | .mirror =>
      cupodTroll_plays_C _ (by decide)

/-- **τ(CupodTroll)'s row** — the matrix-facing statement (`@[tau_row]`: validated by
    `Tau/Lint.lean`, exported to the app): unconditional at large `k`, the floors and
    Löb gates discharged inside. The former literal `VoteBits` list is `RowSpec.bits`. -/
@[tau_row]
theorem cupodTrollRowSpec : RowSpec .cupodTroll tauOrder cupodTrollRow := ⟨2, fun k hk T _ => cupodTrollRow_plays (by omega) T⟩

/-- **τ(CupodTrollBot)**: cooperates up to `trollMass` — everything but the
    weight of the one hypothesis it convicts. -/
theorem tauCupodTroll_phase {k : Nat} (hk : 3 ≤ k) (w : Tmpl → Nat) (θ : Nat)
    (opponent : Prog) :
    (θ ≤ bitMass w cupodTrollRow tauOrder →
      ∃ N, play N (TauBotZ k .cupodTroll w θ) opponent = some .C)
    ∧ (¬ θ ≤ bitMass w cupodTrollRow tauOrder →
      ∃ N, play N (TauBotZ k .cupodTroll w θ) opponent = some .D) :=
  phase_of_bits (tauZoo k) .cupodTroll w cupodTrollRow tauOrder θ opponent
    (fun T _ => cupodTrollRow_plays hk T)

end PD.Tau
