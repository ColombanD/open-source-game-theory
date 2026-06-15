import PrisonersDilemma.Program
import PrisonersDilemma.Bots.DefectBot

open PD
namespace PD.Bots

/-- PrudentBot (Critch 2022): cooperate iff it can prove BOTH that the opponent
    cooperates with it AND that the opponent defects against DefectBot (so it is
    not a sucker), otherwise defect.

    The cooperation `.search` is kept at the *root* — the same shape DupocBot
    uses — so the Löb cooperation fixed point `□φ → φ` stays clean and provable
    (a prudence `.ite` wrapping the search would block it). The prudence check is
    folded into the THEN branch as an inner `.search`. -/
def PrudentBot (k : Nat) : Prog :=
  .search k
    (.plays .opp .self Action.C)        -- can I prove opp cooperates with me?
    (.search k                          -- ...if so, also check opp is not a sucker
      (.plays .opp (.bot DefectBot) Action.D)  -- can I prove opp defects vs DefectBot?
      (.const Action.C)                 -- both proven → cooperate
      (.const Action.D))                -- opp is exploitable → defect
    (.const Action.D)                   -- can't prove opp cooperates → defect

end PD.Bots
