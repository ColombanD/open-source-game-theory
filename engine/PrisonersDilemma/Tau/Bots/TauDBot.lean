import PrisonersDilemma.Tau.Roster

/-!
# TauDBot — the defection-punisher, lifted

Base DBot is ONE `.sim` watch with a trusting default: "simulate the opponent
against DefectBot; if they cooperate even with a defector, punish (D); else
cooperate". So the lift is a single `run` stage on the δ_D column, `test = .C`,
`fire = .D`, default `.C` — structurally EBot's first stage with a constant tail
instead of a reciprocity stage.

**Why it was the last non-`.sys` bot to land (2026-08-19).** Its δ_L cell —
"does DBot, seeing Dupoc, provably cooperate?" — is a Gödelian floor of the
EMBEDDED kind: DBot's cooperation is reached by its watch FALLING, and the
watched instance `inst .dupoc .defect` is a budget-`k` searcher whose D-play
certificate pays the `search_f` floor. The census kernel for that shape
(`no_provable_botRunStage_C`) is the single-stage twin of the two-stage one the
run-mode EBot fix forced; before it existed this cell had no honest 0-bit.
-/

namespace PD.Tau

/-- τ(DBot): "exploitable? then punish; else trust." -/
def tauDBotSpec : Spec Tmpl :=
  ⟨[⟨.run, .name .defect, .C, .D⟩], .C⟩

end PD.Tau
