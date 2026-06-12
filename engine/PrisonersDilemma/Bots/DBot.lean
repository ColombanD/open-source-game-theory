import PrisonersDilemma.Program
import PrisonersDilemma.Bots.DefectBot

open PD
namespace PD.Bots

-- Bot defects if the opponent cooperates against a defect probe. --
def DBot : Prog :=
  .ite -- If then else
    (.sim .opp (.bot DefectBot)) -- Simulate opponent against DefectBot
    Action.C -- test action C
    (.const Action.D) -- if opponent cooperates, defect
    (.const Action.C) -- else, cooperate

end PD.Bots
