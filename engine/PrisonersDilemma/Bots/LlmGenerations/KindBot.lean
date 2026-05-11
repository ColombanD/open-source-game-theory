import PrisonersDilemma.Program

open PDNew
namespace PDNew.Bots

/-- KindBot always cooperates, regardless of opponent behavior. -/
def KindBot : Prog := .const Action.C

end PDNew.Bots
