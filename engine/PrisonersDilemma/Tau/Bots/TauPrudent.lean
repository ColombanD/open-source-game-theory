import PrisonersDilemma.Tau.Roster

/-!
# τ(PrudentBot), Critch's canonical bot

Base `PrudentBot k`: cooperate iff the opponent provably cooperates with me AND
provably defects against the defector. The inner search sits in the outer's
then-branch, as in the base source. Base results stagger its budget
(`PrudentBot (2k+64)`); the tau zoo uses one shared `k`, and the cells that
need the stagger are recorded in `app`'s whitelist.
-/

namespace PD.Tau

/-- τ(PrudentBot): cooperates with me and is no sucker, both provably? then C, else D. -/
def tauPrudentSpec : Spec Tmpl :=
  .search .prove .self .C
    (.search .prove (.name .defect) .D (.const .C) (.const .D))
    (.const .D)

end PD.Tau
