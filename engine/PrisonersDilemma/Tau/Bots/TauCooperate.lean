import PrisonersDilemma.Tau.Roster

/-!
# TauCooperate — the unconditional cooperator, lifted

No probe stages: the signal is ignored and every instance plays C. The lift of a
constant is constant — in particular it is α-INDEPENDENT (it cooperates even where a
mass-0 voting bot would not), which is the recorded α = 0 divergence from Def 3's
uniform lift.
-/

namespace PD.Tau

/-- τ(CooperateBot): empty cascade, default C. -/
def tauCoopSpec : Spec Tmpl := ⟨[], .C⟩

end PD.Tau
