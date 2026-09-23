import PrisonersDilemma.Tau.Roster

/-!
# τ(DIMCID), the conditional defector

Base `DIMCID k = .search k (.impl (.plays .self .opp C) (.plays .opp .self D)) (const D) (const C)`:
defect iff my cooperating provably meets defection. CIMCIC's guard with the
opposite consequent — `Mode.proveImplD`. Its diagonal is a real Löb fixpoint on
defection (the two sides name the same player at opposite actions, so `implRefl`
does not apply).
-/

namespace PD.Tau

/-- τ(DIMCID): my cooperation provably meets defection? then D, else C. -/
def tauDIMCIDSpec : Spec Tmpl :=
  .search .proveImplD .self .C (.const .D) (.const .C)

end PD.Tau
