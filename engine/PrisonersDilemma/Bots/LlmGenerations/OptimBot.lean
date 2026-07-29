import PrisonersDilemma.Program

open PD
namespace PD.Bots

/-- OptimBot: lock in the best provable outcome, in payoff order.

    Preference ladder over full outcomes (my play, opponent's play):
      1. (D, C) — exploit:     if provable, play D
      2. (C, C) — cooperate:   if provable, play C
      3. (D, D) — safe defect: if provable, play D
      4. fallback:             play C

    `Formula` has no conjunction, so each rung "outcome (a, b) is provable"
    is two nested `.search`es (the PrudentBot idiom): the opponent's play is
    the outer guard, my own play the inner one. A rung falls through to the
    next rung whenever EITHER conjunct is unprovable, so the continuation
    sits in both else slots. The action a rung commits to always equals its
    own-play conjunct, keeping every branch consistent with what it proved. -/
def OptimBot (k : Nat) : Prog :=
  -- rung 3: (D, D) provable → D, else fallback C
  let rung3 : Prog :=
    .search k (.plays .opp .self Action.D)
      (.search k (.plays .self .opp Action.D)
        (.const Action.D)
        (.const Action.C))
      (.const Action.C)
  -- rung 2: (C, C) provable → C, else rung 3
  let rung2 : Prog :=
    .search k (.plays .opp .self Action.C)
      (.search k (.plays .self .opp Action.C)
        (.const Action.C)
        rung3)
      rung3
  -- rung 1: (D, C) provable → D, else rung 2
  .search k (.plays .opp .self Action.C)
    (.search k (.plays .self .opp Action.D)
      (.const Action.D)
      rung2)
    rung2

end PD.Bots
