import PrisonersDilemma.Tau.Roster

/-!
# τ(DupocTrollBot), the identity checker aimed at the Löbian cooperator

Base `DupocTrollBot k = .search k (.eq .opp (DupocBot k)) (const D) (const C)`
(`Bots/DupocTrollBot.lean`, 2026-10-13): defect iff the opponent is literally
DupocBot — the mirror image of CupodTrollBot, which targets CupodBot. The guard is a
syntactic identity test, so the lift uses `Mode.proveEq` on the named target
`.dupoc`: the compiler decides `T = .dupoc` from the index and emits a closed,
decidable `.eq`. The `test` action is unused by this mode.

Added to the roster 2026-10-19 so that the ladder zoo `body8+trolls` has kernel
rows in PA-`S'` (`arith/ArithS/Tau/Rows/DupocTroll.lean`); the engine row here is
the engine-side twin the roster census demands.
-/

namespace PD.Tau

/-- τ(DupocTrollBot): is the hypothesis Dupoc? then D, else C. -/
def tauDupocTrollSpec : Spec Tmpl :=
  .search .proveEq (.name .dupoc) .C (.const .D) (.const .C)

end PD.Tau
