import PrisonersDilemma.Tau.Theorems.Columns

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
  | .guardian | .dbot | .cupodTroll | .cimcic | .dimcid | .prudent | .mirror =>
      cupodTroll_plays_C _ (by decide)

/-- The scanner-facing bit row (read by `app`'s `def4_theorems.py` — keep the
    literal list): `vecOf_bits`' mapped row, by defeq on the concrete zoo. -/
theorem cupodTrollBits {k : Nat} (hk : 3 ≤ k) (w : Tmpl → Nat) :
    VoteBits (vecOf (tauZoo k) .cupodTroll w tauOrder)
      [(w .coop, .C), (w .defect, .C), (w .tftSim, .C), (w .tftPf, .C),
       (w .dupoc, .C), (w .ebot, .C), (w .just, .C), (w .obot, .C),
       (w .guardian, .C), (w .dbot, .C), (w .cupodTroll, .C), (w .cupod, .D), (w .cimcic, .C), (w .dimcid, .C), (w .prudent, .C), (w .mirror, .C)] :=
  vecOf_bits (tauZoo k) .cupodTroll w cupodTrollRow tauOrder
    fun T _ => cupodTrollRow_plays hk T

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
