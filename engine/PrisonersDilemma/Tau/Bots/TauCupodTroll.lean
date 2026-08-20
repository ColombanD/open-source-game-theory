import PrisonersDilemma.Tau.Roster

/-!
# TauCupodTroll — the identity checker, lifted

Base CupodTrollBot: "if the opponent IS literally CupodBot, defect; else cooperate"
— one `.search` whose guard is `.eq .opp (.bot (CupodBot k))`, a SYNTACTIC identity
test rather than a behavioral or modal one.

**The one bot liftable without `.sys`** (2026-08-20). Every other unlifted bot's
guard mentions the opponent's view of ME (`.plays .opp .self …`), which makes it a
self-prober and needs the mutual binder. This guard names a LITERAL third party, so
the compiled instance is closed and grounded — the recursion bottoms out immediately.

**What the lift tests, honestly.** In the tau layer the "opponent" of `inst A T` is
the frozen instance `inst T A`, not a base bot, so the identity question becomes
"is the probed instance syntactically `inst cupodTroll`'s notion of CupodBot?" — and
since CupodBot is NOT in the tau zoo (it is `.sys`-blocked), the answer is uniformly
NO. τ(CupodTroll) therefore cooperates with every hypothesis in the CURRENT zoo: it
is a constant-C bot here, and only becomes interesting once CupodBot lands. That is
recorded rather than hidden — the row is honest, not vacuous, and it will change
shape exactly when `.sys` admits its target.
-/

namespace PD.Tau

/-- τ(CupodTrollBot): "is my opponent literally CupodBot? then D, else C." -/
def tauCupodTrollSpec : Spec Tmpl :=
  ⟨[⟨.proveEq, .name .dupoc, .C, .D⟩], .C⟩

end PD.Tau
