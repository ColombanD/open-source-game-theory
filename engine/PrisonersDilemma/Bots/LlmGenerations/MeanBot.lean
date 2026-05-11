import PrisonersDilemma.Program

open PDNew
namespace PDNew.Bots

/-- MeanBot always defects, regardless of opponent behavior. -/
def MeanBot : Prog := .const Action.D

end PDNew.Bots
