import PrisonersDilemma.Program

open PD
namespace PD.Bots

/-- OptimBot: an outcome-optimizer with two separate proof budgets.

    `kOpp` bounds all reasoning about the *opponent* (the outer probe of each
    rung); `kSelf` (intended to be strictly larger) bounds all reasoning about
    *itself* (the inner self-proof). Self-proofs must trace this bot's own
    evaluation, including FAILED opponent probes, and each failed probe costs
    the full `kOpp` (the `search_f` cost floor) — so `kSelf` needs to sit a
    large linear factor above `kOpp` for the rung-3 Löb bootstrap to land.
    `OptimBot k k` recovers the old uniform-budget bot; same two-tier move as
    `PrudentBot2 (kOut kIn)`.

    Preference ladder over full outcomes (my play, opponent's play):
      1. (D, C) — exploit:     if provable, play D
      2. (C, C) — cooperate:   if provable, play C
      3. (D, D) — safe defect: if provable, play D
      4. fallback:             play C

    `Formula` has no conjunction, so each rung "outcome (a, b) is provable"
    is two nested `.search`es (the PrudentBot idiom): the opponent's play is
    the outer guard at `kOpp`, my own play the inner one at `kSelf`. A rung
    falls through to the next rung whenever EITHER conjunct is unprovable, so
    the continuation sits in both else slots. The action a rung commits to
    always equals its own-play conjunct — `.const` sits immediately under the
    self-proof — keeping every branch consistent with what it proved. -/
def OptimBot (kOpp kSelf : Nat) : Prog :=
  -- rung 3: (D, D) provable → D, else fallback C
  let rung3 : Prog :=
    .search kOpp (.plays .opp .self Action.D)
      (.search kSelf (.plays .self .opp Action.D)
        (.const Action.D)
        (.const Action.C))
      (.const Action.C)
  -- rung 2: (C, C) provable → C, else rung 3
  let rung2 : Prog :=
    .search kOpp (.plays .opp .self Action.C)
      (.search kSelf (.plays .self .opp Action.C)
        (.const Action.C)
        rung3)
      rung3
  -- rung 1: (D, C) provable → D, else rung 2
  .search kOpp (.plays .opp .self Action.C)
    (.search kSelf (.plays .self .opp Action.D)
      (.const Action.D)
      rung2)
    rung2

end PD.Bots
