import PrisonersDilemma.Tau.Roster

/-!
# τ(MirrorBot) — the forwarder

Base `MirrorBot = .sim .opp .self`: "simulate my OPPONENT against ME, and play
whatever it plays." No branches, no proof search — the simplest reflective bot in
the zoo, and the one the whole `.sim` modality exists for.

The lift is `Spec.sim .self` — literally the base source with the `.opp` hole
filled: at hypothesis `T` it compiles to a bare `.sim (.bot (inst T .mirror))
(.bot (inst T .mirror))`, "the signal I am treating, facing me", and plays what
that plays. A FORWARDER, not a classifier: the zoo's only bot with no `test`, no
`fire`, no fall-through.

**Why not a `run` stage.** Until 2026-08-24 the DSL was a list of stages and the
mirror was encoded as `⟨.run, .self, .C, .C⟩` with default `D` — a threshold test
that agrees with copying on `{C, D}`. Behaviourally identical; intensionally a
different program, and `S` reads programs: a bare `.sim` is legible by ONE rule in
both polarities (`botSysSimStep`, the `.sys` twin of `simStep`), while an `.ite`
needs a rule per branch. The threshold encoding blocked the mirror×cupod cells (a
Löb fixpoint on DEFECTION — the else branch) and forced a then-only engine rule.
The tree DSL (`Tau/Spec.lean`) was introduced so this bot could be written as
what it is; the forwarder encoding closes all three entangled mirror pairs by
the same single-formula Löb engine (`Tau/Theorems/TauMirror/Helpers`).

**Non-termination is inherited, deliberately.** The diagonal compiles to
`.sim .self .self`, i.e. base MirrorBot's self-play, whose `outcome` is proven
`none`. So `inst .mirror .mirror` genuinely does not evaluate — the one zoo cell
with no play, and the reason τ(Mirror)'s own `VoteBits` row is unstateable. Every
OTHER cell terminates, because the watched instance is some other template's.

This is the template EBot's third branch needs: base EBot's last branch sims
MirrorBot, and until `.mirror` existed that branch could not be written, which
was the whole content of the former `(TauEBot, TauEBot)` whitelist entry.
-/

open PD

namespace PD.Tau

/-- τ(MirrorBot)'s spec: the bare forwarder — base `.sim .opp .self` with the hole filled. -/
def tauMirrorSpec : Spec Tmpl := .sim .self

end PD.Tau
