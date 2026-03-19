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

/-- Canonical one-shot PD matrix: CC=3, CD=0, DC=5, DD=1. -/
def canonicalPayoff : PayoffMatrix :=
  { cc := 3, cd := 0, dc := 5, dd := 1 }

def payoff (m : PayoffMatrix) (mine opp : Action) : Nat :=
  match mine, opp with
  | C, C => m.cc
  | C, D => m.cd
  | D, C => m.dc
  | D, D => m.dd

@[simp] theorem payoff_canonical_cc : payoff canonicalPayoff C C = 3 := rfl
@[simp] theorem payoff_canonical_cd : payoff canonicalPayoff C D = 0 := rfl
@[simp] theorem payoff_canonical_dc : payoff canonicalPayoff D C = 5 := rfl
@[simp] theorem payoff_canonical_dd : payoff canonicalPayoff D D = 1 := rfl

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
