import PrisonersDilemma.Tau.Roster

/-!
# τ(DBot), the sucker-punisher

Base `DBot = .ite (.sim .opp (.bot DefectBot)) C (const D) (const C)`: if the
opponent cooperates even with the defector, punish; else cooperate. One `.sim`
watch on the δ_D column, lifted verbatim.
-/

namespace PD.Tau

/-- τ(DBot): cooperates with the defector? then D, else C. -/
def tauDBotSpec : Spec Tmpl :=
  .ite (.sim (.name .defect)) .C (.const .D) (.const .C)

end PD.Tau
