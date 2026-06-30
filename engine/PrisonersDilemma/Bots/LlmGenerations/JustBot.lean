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

end PD.Bots
