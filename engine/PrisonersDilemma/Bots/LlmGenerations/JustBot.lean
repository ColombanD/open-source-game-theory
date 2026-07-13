import PrisonersDilemma.Program
import PrisonersDilemma.Bots.DupocBot

open PD
namespace PD.Bots

/-- JustBot: Cooperate if we can prove the opponent will cooperate against DupocBot,
    otherwise defect.

    The reference to DupocBot is wrapped in `.bot` so that `subst` treats it as a
    *closed bot reference* — a scope barrier (see `Prog.subst` / the `.bot` notes in
    `Program.lean`). Without it, evaluating JustBot would `subst` the players into
    DupocBot's own `.self`/`.opp` placeholders, mutating it into a different program;
    `.bot` freezes it so the guard genuinely asks "does the opponent cooperate against
    *DupocBot*?". This is the same barrier TitForTatBot uses for `.bot CooperateBot`;
    it is needed for any literal bot reference in source, not only inside `.sim`. -/
def JustBot (k : Nat) : Prog :=
  .search k
    (.plays .opp (.bot (DupocBot k)) Action.C)
    (.const Action.C)
    (.const Action.D)

/-- **Two-tier JustBot** (the FREEZE TRICK, 2026-07-09): search budget `K` decoupled
    from the frozen snapshot's budget `k`. `JustBot k = JustBot2 k k`.

    Why: the guard fact "opp cooperates with `.bot (DupocBot k)`" costs `k + O(log k)`
    for simulator opponents (their play crosses the snapshot's failed probe search —
    the `search_f` floor `k`). With one parameter the asking budget equals the floor
    and the guard can never fire (`outcome_JustBot_vs_DBot = (D, C)`); with `K ≥
    k + log₂ k + 26` the certificate fits and cooperation returns
    (`outcome_JustBot2_vs_DBot = (C, C)`). This is the general escape from `.self`
    self-reference: a `.self` guard's floor chases its own budget (one node, one
    dial), but a FROZEN weaker snapshot `.bot (DupocBot k)` points strictly down the
    budget order — the well-founded-hierarchy criterion. Price: the snapshot is not
    the bot ("cooperates with my weaker past self", not "with me") — a spoofing
    surface genuine `.self` guards don't have. -/
def JustBot2 (K k : Nat) : Prog :=
  .search K
    (.plays .opp (.bot (DupocBot k)) Action.C)
    (.const Action.C)
    (.const Action.D)

end PD.Bots
