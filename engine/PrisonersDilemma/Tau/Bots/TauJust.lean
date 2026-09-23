import PrisonersDilemma.Tau.Roster

/-!
# τ(JustBot), the third-party prover

Base `JustBot k = .search k (.plays .opp (.bot (DupocBot k)) C) (const C) (const D)`:
cooperate iff the opponent provably cooperates with Dupoc. The frozen third party
becomes the named target `.dupoc`, so it reads the same δ_L column τ(Dupoc) does,
including Dupoc's Löb-gated diagonal bit.
-/

namespace PD.Tau

/-- τ(JustBot): provably cooperates with Dupoc? then C, else D. -/
def tauJustSpec : Spec Tmpl :=
  .search .prove (.name .dupoc) .C (.const .C) (.const .D)

end PD.Tau
