import PrisonersDilemma.Program

open PD
namespace PD.Bots

/-- WaryBot: defect iff I can REFUTE your cooperation; else cooperate.

    The refutation twin of CupodBot. CupodBot's guard asserts the opponent's
    defection (`.plays .opp .self D`); WaryBot's guard is the NEGATION of the
    opponent's cooperation (`.neg (.plays .opp .self C)`). With two actions the
    two guards are semantically equivalent — ¬(plays C) and (plays D) have the
    same `interp` — but they are DIFFERENT formulas, proved through different
    machinery: the positive atom goes through `PlaysProof`, the negation through
    the refutation suppliers (`atomNeg`) and the family-B rules (`negElim`,
    `contrapose`). No other bot in the zoo puts `.neg` in a guard.

    The study: run WaryBot and CupodBot against the same opponents. Every
    matchup where they agree is evidence the assertion and refutation layers of
    `S` are equally strong at that budget; any divergence is a machine-checked
    theorem locating a gap between proving `plays D` and refuting `plays C`. -/
def WaryBot (k : Nat) : Prog :=
  .search k
    (.neg (.plays .opp .self Action.C))
    (.const Action.D)
    (.const Action.C)

end PD.Bots
