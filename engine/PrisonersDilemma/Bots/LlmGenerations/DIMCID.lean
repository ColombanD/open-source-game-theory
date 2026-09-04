import PrisonersDilemma.Program

open PD
namespace PD.Bots

/-- DIMCID: Defect If My Cooperation Implies Defection.
    Uses the proof oracle to check whether "if I cooperate, the opponent defects".
    If `S` derives that implication within budget k (`⊢_k`), defect; otherwise cooperate. -/
def DIMCID (k : Nat) : Prog :=
  .search k
    (.impl (.plays .self .opp Action.C) (.plays .opp .self Action.D))
    (.const Action.D)
    (.const Action.C)

end PD.Bots
