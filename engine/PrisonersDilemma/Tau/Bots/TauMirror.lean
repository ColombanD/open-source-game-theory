import PrisonersDilemma.Tau.Roster

/-!
# τ(MirrorBot) — the pure copier

Base `MirrorBot = .sim .opp .self`: "simulate my OPPONENT against ME, and play
whatever it plays." No branches, no proof search — the simplest reflective bot in
the zoo, and the one the whole `.sim` modality exists for.

The lift is a single `run` stage on the SELF target: at hypothesis `T` it watches
`inst T .mirror` — "the signal I am treating, facing me" — in the frozen self
frame every probe uses. Firing `C` on `C` and defaulting to `D` reproduces
COPYING exactly on `{C, D}`, the same encoding τ(TFTSim) uses for its own watch.

**Non-termination is inherited, deliberately.** The diagonal compiles to
`.ite (.sim .self .self) …`, i.e. base MirrorBot's self-play, whose `outcome` is
proven `none`. So `inst .mirror .mirror` genuinely does not evaluate — the one
zoo cell with no play. Every OTHER cell terminates, because the watched instance
is some other template's, and those are all terminating.

This is the template EBot's third stage needs: base EBot's last branch sims
MirrorBot, and until `.mirror` existed that stage could not be written, which is
the whole content of the `(TauEBot, TauEBot)` whitelist entry.
-/

open PD

namespace PD.Tau

/-- τ(MirrorBot)'s spec: one `run` stage on the self target, copying. -/
def tauMirrorSpec : Spec Tmpl :=
  ⟨[⟨.run, .self, .C, .C⟩], .D⟩

end PD.Tau
