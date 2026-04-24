import PrisonersDilemma.Program
import PrisonersDilemma.Bots.CooperateBot
import PrisonersDilemma.Bots.DefectBot
import PrisonersDilemma.Bots.MirrorBot

open PDNew
namespace PDNew.Bots

def _EBot : Prog :=
  .ite -- If then else
    (.sim .opp DefectBot) -- Simulate opponent against DefectBot
    Action.C -- test action C
    (.const Action.D) -- if opponent cooperates, defect
    (.ite -- else, simulate opponent against CooperateBot
      (.sim .opp CooperateBot)
      Action.C -- test action C
      (.const Action.C) -- if opponent cooperates, cooperate
      (.ite -- else, simulate opponent against MirrorBot
        (.sim .opp MirrorBot)
        Action.C -- test action C
        (.const Action.C) -- if opponent cooperates, cooperate
        (.const Action.D))) -- else, defect

end PDNew.Bots
