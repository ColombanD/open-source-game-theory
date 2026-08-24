import PrisonersDilemma.Tau.Roster

/-!
# TauOBot — the behavioral defection-detector, lifted

Base OBot: "if the opponent defects against CooperateBot, defect; else if it defects
against DefectBot, defect; else cooperate" — cooperation only with those who
cooperate with EVERYONE probed. Two `run` stages with `test = .D` (the first lifted
bot to need the test field): it watches for DEFECTION and fires D on seeing it.
Being behavioral it reads TRUE plays — floor-blind — but its standard is so strict
that on this zoo it cooperates with the unconditional cooperator alone
(everyone else defects against a defector), giving the zoo's narrowest boundary:
`θ ≤ w .coop`.
-/

namespace PD.Tau

/-- τ(OBot): "defects vs Coop? → D; defects vs Defect? → D; else C." -/
def tauOBotSpec : Spec Tmpl :=
  .ite (.sim (.name .coop)) .D (.const .D)
    (.ite (.sim (.name .defect)) .D (.const .D) (.const .C))

end PD.Tau
