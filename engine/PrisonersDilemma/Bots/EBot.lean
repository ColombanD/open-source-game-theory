import PrisonersDilemma.Program
import PrisonersDilemma.Bots.CooperateBot
import PrisonersDilemma.Bots.DefectBot
import PrisonersDilemma.Bots.MirrorBot

open PD
namespace PD.Bots

def EBot : Prog :=
  .ite -- If then else
    (.sim .opp (.bot DefectBot)) -- Simulate opponent against DefectBot
    Action.C -- test action C
    (.const Action.D) -- if opponent cooperates, defect
    (.ite -- else, simulate opponent against CooperateBot
      (.sim .opp (.bot CooperateBot))
      Action.C -- test action C
      (.const Action.C) -- if opponent cooperates, cooperate
      (.ite -- else, simulate opponent against MirrorBot
        (.sim .opp (.bot MirrorBot))
        Action.C -- test action C
        (.const Action.C) -- if opponent cooperates, cooperate
        (.const Action.D))) -- else, defect

end PD.Bots
