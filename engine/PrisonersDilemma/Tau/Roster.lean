import PrisonersDilemma.Tau.Spec

/-!
# Tau/Roster — the cast list of the six-template tau zoo

The one structural difference from the base-bot layout, and why this file must
exist BEFORE the per-bot files: a base bot references another bot by IMPORTING its
finished term, but a tau spec references other bots by NAME in a shared index (a
stage target like `.name .coop`), resolved later by the compiler — that indirection
is what makes mutual reference expressible at all. So the roster is declared first,
each `Tau/Bots/<TauBot>.lean` writes its spec against it, and `Tau/Zoo.lean` glues
the rows into the zoo. Adding a bot touches exactly: one constructor here, one new
bot file, one arm in `Zoo.lean`.
-/

namespace PD.Tau

/-- The six templates. (A readable enum, not `Fin 6` — roadmap open question 5.) -/
inductive Tmpl | coop | defect | tftSim | tftPf | dupoc | ebot
deriving DecidableEq, Repr

/-- The canonical hypothesis order — the entry order of every decision vector. -/
def order6 : List Tmpl := [.coop, .defect, .tftSim, .tftPf, .dupoc, .ebot]

end PD.Tau
