import PrisonersDilemma.Program

open PD
namespace PD.Bots

/-- CIMCIC: Cooperate if I can prove my cooperation implies cooperation from the opponent.
    Uses the proof oracle `proofSearch` to check whether `S` derives the formula
    (I cooperate → opponent cooperates) within budget k (`⊢_k`). -/
def CIMCIC (k : Nat) : Prog :=
  .search k
    (.impl (.plays .self .opp Action.C) (.plays .opp .self Action.C))
    (.const Action.C)
    (.const Action.D)

end PD.Bots
