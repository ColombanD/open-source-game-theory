import PrisonersDilemma.Tau.Roster

/-!
# τ(DefectBot)

Base `DefectBot = .const D`. The lift of a constant is the constant: every
instance plays D.
-/

namespace PD.Tau

/-- τ(DefectBot): always D. -/
def tauDefectSpec : Spec Tmpl := .const .D

end PD.Tau
