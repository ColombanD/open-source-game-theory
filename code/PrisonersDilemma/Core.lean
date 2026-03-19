namespace PD

inductive Action : Type where
  | C : Action
  | D : Action
  deriving DecidableEq, Repr

open Action

/-- One-shot Prisoner's Dilemma payoff matrix. -/
structure PayoffMatrix : Type where
  cc : Nat
  cd : Nat
  dc : Nat
  dd : Nat
  deriving Repr

/-- Canonical matrix used in your markdown notes: CC=2, CD=0, DC=3, DD=1. -/
def canonicalPayoff : PayoffMatrix :=
  { cc := 2, cd := 0, dc := 3, dd := 1 }

def payoff (m : PayoffMatrix) (mine opp : Action) : Nat :=
  match mine, opp with
  | C, C => m.cc
  | C, D => m.cd
  | D, C => m.dc
  | D, D => m.dd

structure Outcome : Type where
  leftAction : Action
  rightAction : Action
  leftPayoff : Nat
  rightPayoff : Nat
  deriving Repr

def mkOutcome (m : PayoffMatrix) (leftAction rightAction : Action) : Outcome :=
  {
    leftAction := leftAction
    rightAction := rightAction
    leftPayoff := payoff m leftAction rightAction
    rightPayoff := payoff m rightAction leftAction
  }

end PD
