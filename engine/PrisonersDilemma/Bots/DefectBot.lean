import PrisonersDilemma.Program

open PDNew
namespace PDNew.Bots

/-- DefectBot always defects, regardless of opponent behavior. -/
def DefectBot : Prog := .const Action.D

end PDNew.Bots
