import PrisonersDilemma.Program
import PrisonersDilemma.Bots.CupodBot
import PrisonersDilemma.Bots.DupocBot

open PD
namespace PD.Bots

-- Defect iff the opponent is literally CupodBot (structural identity).
-- The guard's RHS is a frozen literal: `subst` resolves `.opp` to the concrete
-- opponent but leaves `CupodBot k` untouched, so the test compares the real
-- opponent's source against the literal CupodBot.
def CupodTrollBot (k : Nat) : Prog :=
  .search k
    (.eq .opp (CupodBot k)) -- test if opponent is literally CupodBot
    (.const Action.D)
    (.const Action.C) -- else, cooperate

end PD.Bots
