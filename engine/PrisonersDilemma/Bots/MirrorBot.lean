import PrisonersDilemma.Program
import PrisonersDilemma.Derivation

open PD
namespace PD.Bots

/-- MirrorBot: mimics what the opponent does against itself-/
def MirrorBot : Prog :=
  .sim .opp .self -- Simulate opponent against itself

end PD.Bots
