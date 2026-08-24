import PrisonersDilemma.Tau.Roster

/-!
# TauDefect — the unconditional defector, lifted

No probe stages: every instance plays D, at every α — including α = 0, where Def 3's
uniform lift of DefectBot would cooperate on its empty mass (the recorded α = 0
constant artifact).
-/

namespace PD.Tau

/-- τ(DefectBot): empty cascade, default D. -/
def tauDefectSpec : Spec Tmpl := .const .D

end PD.Tau
