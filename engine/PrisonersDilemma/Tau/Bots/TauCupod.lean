import PrisonersDilemma.Tau.Roster

/-!
# TauCupod — the suspicious cooperator, lifted (the FIRST `.sys` bot)

Base CupodBot: "cooperate UNLESS I can prove the opponent defects against me" —
one `.search` on `.plays .opp .self D`, punishing on proof and trusting by default.
It is τ(Dupoc)'s exact mirror: same self-probe geometry, opposite polarity
(Dupoc proves COOPERATION and fires C; Cupod proves DEFECTION and fires D).

**Why this bot needed the binder.** Its stage targets `self`, and so does
TauDupoc's (and TauJust's, by name). Two self-probers means
`inst cupod dupoc ⊃ inst dupoc cupod ⊃ inst cupod dupoc` — no finite tree. Since
2026-08-20 the compiler detects the entanglement (`Zoo.entangled`) and emits a
2-member `.sys` system whose members reference each other by `.selfIdx` index. This
is the bot the whole `.sys` revival was for.

**The red-cell connection.** `(CupodBot, DupocBot)` is Critch's open problem, proven
in the BASE library on 2026-08-20 via the τ-transposition
(`outcome_DupocBot_vs_CupodBot = (D, C)` at every same-`k`). The tau lift asks the
same question one level up, where the two instances are now literally components of
one system.
-/

namespace PD.Tau

/-- τ(CupodBot): "provably defects against me? then D, else C." -/
def tauCupodSpec : Spec Tmpl :=
  ⟨[⟨.prove, .self, .D, .D⟩], .C⟩

end PD.Tau
