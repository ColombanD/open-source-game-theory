import PrisonersDilemma.Tau.Roster

/-!
# τ(CooperateBot)

Base `CooperateBot = .const C`. The lift of a constant is the constant: the
signal is ignored and every instance plays C.
-/

namespace PD.Tau

/-- τ(CooperateBot): always C. -/
def tauCoopSpec : Spec Tmpl := .const .C

end PD.Tau
