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

/-- τ(CupodTroll)'s bit ROW: C everywhere — the identity check never fires. -/
def cupodTrollRow : Tmpl → Action := fun _ => .C

theorem cupodTrollRow_plays (k : Nat) :
    ∀ T, ∃ N, eval N (.bot (inst (tauZoo k) .cupodTroll T))
              (.bot (inst (tauZoo k) .cupodTroll T))
              (inst (tauZoo k) .cupodTroll T) = some (cupodTrollRow T) :=
  fun T => cupodTroll_plays_C T

/-- The scanner-facing bit row (read by `app`'s `def4_theorems.py` — keep the
    literal list): `vecOf_bits`' mapped row, by defeq on the concrete zoo. -/
theorem cupodTrollBits (k : Nat) (w : Tmpl → Nat) :
    VoteBits (vecOf (tauZoo k) .cupodTroll w tauOrder)
      [(w .coop, .C), (w .defect, .C), (w .tftSim, .C), (w .tftPf, .C),
       (w .dupoc, .C), (w .ebot, .C), (w .just, .C), (w .obot, .C),
       (w .guardian, .C), (w .dbot, .C), (w .cupodTroll, .C)] :=
  vecOf_bits (tauZoo k) .cupodTroll w cupodTrollRow tauOrder
    fun T _ => cupodTrollRow_plays k T

/-- **τ(CupodTrollBot)**: cooperates at every θ within the total mass. -/
theorem tauCupodTroll_phase (k : Nat) (w : Tmpl → Nat) (θ : Nat) (opponent : Prog) :
    (θ ≤ bitMass w cupodTrollRow tauOrder →
      ∃ N, play N (TauBotZ k .cupodTroll w θ) opponent = some .C)
    ∧ (¬ θ ≤ bitMass w cupodTrollRow tauOrder →
      ∃ N, play N (TauBotZ k .cupodTroll w θ) opponent = some .D) :=
  phase_of_bits (tauZoo k) .cupodTroll w cupodTrollRow tauOrder θ opponent
    (fun T _ => cupodTrollRow_plays k T)

end PD.Tau
