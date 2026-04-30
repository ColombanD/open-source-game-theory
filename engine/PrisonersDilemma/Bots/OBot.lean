import PrisonersDilemma.Program
import PrisonersDilemma.Bots.DefectBot
import PrisonersDilemma.Bots.CooperateBot

open PDNew
namespace PDNew.Bots

/-- Strategy definition for OBot.
OBot probes the opponent's response to CooperateBot and DefectBot, and then chooses its action based on the opponent's behavior. -/
def OBot : Prog :=
  .ite -- If then else
    (.sim .opp (.bot CooperateBot)) -- Simulate opponent against CooperateBot
    Action.C -- Test action C
    (.ite -- If opponent cooperates against CooperateBot
      (.sim .opp (.bot DefectBot)) -- Ask: What does opponent do against DefectBot?
      Action.C -- Test action C
      (.const Action.C) -- If opponent cooperates against DefectBot, cooperate
      (.const Action.D )) -- If opponent defects against DefectBot, defect
    (.const Action.D) -- If opponent defects against CooperateBot, defect
