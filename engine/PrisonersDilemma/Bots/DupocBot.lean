import PrisonersDilemma.Program

open PD
namespace PD.Bots

-- Defect unless proof of opponent cooperating is found within k steps.
def DupocBot (k : Nat) : Prog :=
  .search k
    (.plays .opp .self Action.C)
    (.const Action.C)
    (.const Action.D)

end PD.Bots
