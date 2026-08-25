import PrisonersDilemma.Tau.Roster

/-!
# τ(CIMCIC), the conditional cooperator

Base `CIMCIC k = .search k (.impl (.plays .self .opp C) (.plays .opp .self C)) (const C) (const D)`:
cooperate iff my cooperation provably implies theirs. `Mode.proveImpl` keeps the
antecedent's subject as the `.self` pronoun and fills the other slot with the
hypothesis. On its diagonal the guard is `φ → φ`, closed by `implRefl` — no Löb.
-/

namespace PD.Tau

/-- τ(CIMCIC): my cooperation provably implies theirs? then C, else D. -/
def tauCIMCICSpec : Spec Tmpl :=
  .search .proveImpl .self .C (.const .C) (.const .D)

end PD.Tau
