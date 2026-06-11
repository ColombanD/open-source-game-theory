import PrisonersDilemma.Program
import PrisonersDilemma.Bots.DupocBot

open PD
namespace PD.Bots

/-- JustBot: Cooperate if we can prove the opponent will cooperate against DupocBot,
    otherwise defect. -/
def JustBot (k : Nat) : Prog :=
  .search k
    (.plays .opp (DupocBot k) Action.C)
    (.const Action.C)
    (.const Action.D)

end PD.Bots
