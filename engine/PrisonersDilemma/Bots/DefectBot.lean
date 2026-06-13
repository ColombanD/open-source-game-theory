import PrisonersDilemma.Program

open PD
namespace PD.Bots

/-- DefectBot always defects, regardless of opponent behavior. -/
def DefectBot : Prog := .const Action.D

end PD.Bots
