import PrisonersDilemmaNew.Program

open PDNew
namespace PDNew.Bots

-- Cooperate unless proof of opponent defecting is found within k steps.
def CupodBot (k : Nat) : Prog :=
  .search k
    (.plays .opp .self Action.D)
    (.const Action.D)
    (.const Action.C)

end PDNew.Bots
