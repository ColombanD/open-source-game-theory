import PrisonersDilemma.Program
import PrisonersDilemma.Bots.DupocBot

open PD

namespace PD.Bots

-- Defect iff the opponent is literally DupocBot (structural identity) — the troll aimed at the
-- Löbian cooperator, the mirror image of `CupodTrollBot` (which targets CupodBot).
-- The guard's RHS is a frozen literal: `subst` resolves `.opp` to the concrete opponent but
-- leaves `DupocBot k` untouched, so the test compares the real opponent's source against the
-- literal DupocBot. Against everyone else the `.eq` guard is false, hence (by soundness)
-- unprovable, and the bot cooperates. Added 2026-10-13; its cells live in PA-`S'` only
-- (`arith/ArithS/Cells/DupocTrollBot.lean`) — there is no engine theorem about it.
def DupocTrollBot (k : Nat) : Prog :=
  .search k
    (.eq .opp (DupocBot k)) -- test if opponent is literally DupocBot
    (.const Action.D)       -- if so, defect
    (.const Action.C)       -- else, cooperate

end PD.Bots
