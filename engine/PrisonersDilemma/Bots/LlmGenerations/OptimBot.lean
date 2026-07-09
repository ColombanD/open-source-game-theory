-- Need to define the ∧ operator in the Formula namespace

import PrisonersDilemma.Program

open PD
namespace PD.Bots

/-- OptimBot:
      - If proof of (D, C), play D
      - If proof of (C, C), play C
      - If proof of (D, D), play D
      - Else, play C -/
def OptimBot (k : Nat) : Prog :=
  .search k
    ((.plays .self .opp Action.D) ∧ (.plays .opp .self Action.C))
    (.const Action.D)
    (.search k
      ((.plays .self .opp Action.C) ∧ (.plays .opp .self Action.C))
      (.const Action.C)
      (.search k
        ((.plays .self .opp Action.D) ∧ (.plays .opp .self Action.D))
        (.const Action.D)
        (.const Action.C)))

end PD.Bots
