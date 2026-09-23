import PrisonersDilemma.Tau.Roster

/-!
# τ(OBot), the behavioral defection-detector

Base OBot: defects against the cooperator? then D; else defects against the
defector? then D; else C. Two `.sim` watches testing for DEFECTION, lifted verbatim.
On this zoo it cooperates with the unconditional cooperator alone.
-/

namespace PD.Tau

/-- τ(OBot): defects vs the cooperator or the defector? then D, else C. -/
def tauOBotSpec : Spec Tmpl :=
  .ite (.sim (.name .coop)) .D (.const .D)
    (.ite (.sim (.name .defect)) .D (.const .D) (.const .C))

end PD.Tau
