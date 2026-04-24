import PrisonersDilemma.Program
import PrisonersDilemma.Dynamics

open PDNew
namespace PDNew.Bots

/-- MirrorBot: mimics what the opponent does against itself-/
def MirrorBot : Prog :=
  .sim .opp .self -- Simulate opponent against itself

end PDNew.Bots
