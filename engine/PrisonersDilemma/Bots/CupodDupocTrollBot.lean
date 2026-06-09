import PrisonersDilemma.Program
import PrisonersDilemma.Bots.CupodBot
import PrisonersDilemma.Bots.DupocBot

open PD
namespace PD.Bots

-- Cooperates iff the opponent is literally CooperateBot (structural identity).
-- Uses the proof oracle to check `.eq .opp (.bot CooperateBot)`: after `subst`,
-- `.opp` is replaced by the concrete opponent program, so the oracle only
-- succeeds when that program is exactly `.const Action.C`.
def CupodDupocTrollBot (k : Nat) : Prog :=
  .search k
    (.eq .opp (.bot (CupodBot k))) -- test if opponent is literally CupodBot
    (.const Action.C)
    (.search k
      (.eq .opp (.bot (DupocBot k))) -- else, test if opponent is literally DupocBot
      (.const Action.D)
      (.const Action.C)) -- else, cooperate against everyone else

end PD.Bots
