import PrisonersDilemma.Program
import PrisonersDilemma.Bots.DefectBot

open PD
namespace PD.Bots

def PrudentBot (k : Nat) : Prog :=
  .ite
    (.sim .opp (.bot DefectBot))  -- Simulate opponent against DefectBot
    Action.D                       -- If opponent defects against DefectBot...
    (.search k                     -- ...search for proof that opponent cooperates against me
      (.plays .opp .self Action.C)
      (.const Action.C)            -- If proven, cooperate
      (.const Action.D))           -- If not proven, defect
    (.const Action.D)              -- If opponent cooperates against DefectBot, defect

end PD.Bots
