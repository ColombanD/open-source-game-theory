import PrisonersDilemma.Program

open PD
namespace PD.Bots

/-- CooperateBot always cooperates, regardless of opponent behavior. -/
def CooperateBot : Prog := .const Action.C

end PD.Bots
