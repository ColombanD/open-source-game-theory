import PrisonersDilemmaNew.Program

open PDNew
namespace PDNew.Bots

/-- CooperateBot always cooperates, regardless of opponent behavior. -/
def CooperateBot : Prog := .const Action.C

end PDNew.Bots
