import PrisonersDilemma.Tau.Roster

/-!
# τ(DupocBot), the Löbian cooperator

Base `DupocBot k = .search k (.plays .opp .self C) (const C) (const D)`: cooperate
iff the opponent provably cooperates with me. The lift is a `prove` search on the
self target. Its diagonal is the Löb quine `.plays .self .self C`, closed past a
budget threshold, so its phase theorem is `∃ k₂`-gated.
-/

namespace PD.Tau

/-- τ(DupocBot): provably cooperates with me? then C, else D. -/
def tauDupocSpec : Spec Tmpl :=
  .search .prove .self .C (.const .C) (.const .D)

end PD.Tau
