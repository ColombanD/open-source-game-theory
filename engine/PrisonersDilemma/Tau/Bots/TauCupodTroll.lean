import PrisonersDilemma.Tau.Roster

/-!
# τ(CupodTrollBot), the identity checker

Base `CupodTrollBot k = .search k (.eq .opp (CupodBot k)) (const D) (const C)`:
defect iff the opponent is literally CupodBot. The guard is a syntactic identity
test, so the lift uses `Mode.proveEq` on the named target `.cupod`: the compiler
decides `T = .cupod` from the index and emits a closed, decidable `.eq`. The
`test` action is unused by this mode.
-/

namespace PD.Tau

/-- τ(CupodTrollBot): is the hypothesis Cupod? then D, else C. -/
def tauCupodTrollSpec : Spec Tmpl :=
  .search .proveEq (.name .cupod) .C (.const .D) (.const .C)

end PD.Tau
