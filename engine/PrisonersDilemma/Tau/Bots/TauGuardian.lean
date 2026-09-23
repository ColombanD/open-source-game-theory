import PrisonersDilemma.Tau.Roster

/-!
# τ(GuardianBot), the norm enforcer

Base `GuardianBot k = .search k (.plays .opp (.bot CooperateBot) D) (const D) (const C)`:
punish iff the opponent provably defects against the cooperator; trust otherwise.
Its own C is the else-play of that failed search, so it is never citable within
budget: every prover's bit on Guardian is 0 while its true play is C.
-/

namespace PD.Tau

/-- τ(GuardianBot): provably defects vs the cooperator? then D, else C. -/
def tauGuardianSpec : Spec Tmpl :=
  .search .prove (.name .coop) .D (.const .D) (.const .C)

end PD.Tau
