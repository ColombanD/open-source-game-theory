import PrisonersDilemma.Program

open PDNew
namespace PDNew.Bots

/-- CIMCIC: Cooperate if I can prove my cooperation implies cooperation from the opponent.
    Uses the proof oracle to check whether the formula
    (I cooperate → opponent cooperates) is provable within k steps. -/
def CIMCIC (k : Nat) : Prog :=
  .search k
    (.impl (.plays .self .opp Action.C) (.plays .opp .self Action.C))
    (.const Action.C)
    (.const Action.D)

end PDNew.Bots
