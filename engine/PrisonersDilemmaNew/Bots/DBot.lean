import PrisonersDilemmaNew.Program
import PrisonersDilemmaNew.Bots.DefectBot

open PDNew
namespace PDNew.Bots

-- Bot defects if the opponent cooperates against a defect probe. --
def DBot : Prog :=
  .ite -- If then else
    (.sim .opp (DefectBot)) -- Simulate opponent against DefectBot
    Action.C -- test action C
    (.const Action.D) -- if opponent cooperates, defect
    (.const Action.C) -- else, cooperate

end PDNew.Bots
