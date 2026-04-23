import PrisonersDilemma.Program
import PrisonersDilemma.Bots.CooperateBot

open PDNew
namespace PDNew.Bots

-- Bot cooperates if the opponent cooperates against a cooperate probe. --
def TitForTatBot : Prog :=
  .ite -- If then else
    (.sim .opp (CooperateBot)) -- Simulate opponent against CooperateBot
    Action.C -- test action C
    (.const Action.C) -- if opponent cooperates, cooperate
    (.const Action.D) -- else, defect

end PDNew.Bots
