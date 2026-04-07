namespace PD -- Open the `PD` namespace so all names are grouped under Prisoner's Dilemma.

inductive Action : Type where -- Define a new datatype `Action` (a player's move).
  | C : Action -- Constructor for "cooperate".
  | D : Action -- Constructor for "defect".
  deriving DecidableEq, Repr -- Auto-generate equality decision and printable representation.

open Action -- Bring `C` and `D` into scope without writing `Action.C` / `Action.D`.

/-- One-shot Prisoner's Dilemma payoff matrix. -/
structure PayoffMatrix : Type where -- Record type storing payoff values for all action pairs.
  cc : Nat -- Payoff when both players cooperate (C,C).
  cd : Nat -- Payoff when I cooperate and opponent defects (C,D).
  dc : Nat -- Payoff when I defect and opponent cooperates (D,C).
  dd : Nat -- Payoff when both players defect (D,D).
  deriving Repr -- Auto-generate a readable representation for debugging/printing.

/-- Canonical one-shot PD matrix: CC=3, CD=0, DC=5, DD=1. -/
def canonicalPayoff : PayoffMatrix := -- Define a concrete, standard Prisoner's Dilemma matrix.
  { cc := 3, cd := 0, dc := 5, dd := 1 } -- Fill each field of the matrix record.

def payoff (m : PayoffMatrix) (mine opp : Action) : Nat := -- Compute my payoff from matrix `m` and two actions.
  match mine, opp with -- Case-split on the ordered pair (my action, opponent action).
  | C, C => m.cc -- If both cooperate, return `cc`.
  | C, D => m.cd -- If I cooperate and opponent defects, return `cd`.
  | D, C => m.dc -- If I defect and opponent cooperates, return `dc`.
  | D, D => m.dd -- If both defect, return `dd`.

@[simp] theorem payoff_canonical_cc : payoff canonicalPayoff C C = 3 := rfl -- Simplification lemma for canonical (C,C) case.
@[simp] theorem payoff_canonical_cd : payoff canonicalPayoff C D = 0 := rfl -- Simplification lemma for canonical (C,D) case.
@[simp] theorem payoff_canonical_dc : payoff canonicalPayoff D C = 5 := rfl -- Simplification lemma for canonical (D,C) case.
@[simp] theorem payoff_canonical_dd : payoff canonicalPayoff D D = 1 := rfl -- Simplification lemma for canonical (D,D) case.

structure Outcome : Type where -- Record containing both chosen actions and both resulting payoffs.
  leftAction : Action -- Action chosen by the left player.
  rightAction : Action -- Action chosen by the right player.
  leftPayoff : Nat -- Payoff received by the left player.
  rightPayoff : Nat -- Payoff received by the right player.
  deriving Repr -- Auto-generate readable representation for this record.

def mkOutcome (m : PayoffMatrix) (leftAction rightAction : Action) : Outcome := -- Build a full `Outcome` from actions and a payoff matrix.
  { -- Start a record literal of type `Outcome`.
    leftAction := leftAction -- Store the provided left player's action.
    rightAction := rightAction -- Store the provided right player's action.
    leftPayoff := payoff m leftAction rightAction -- Left payoff uses (left,right) ordering.
    rightPayoff := payoff m rightAction leftAction -- Right payoff swaps order to evaluate from right player's perspective.
  } -- End the `Outcome` record literal.

end PD -- Close the `PD` namespace.
