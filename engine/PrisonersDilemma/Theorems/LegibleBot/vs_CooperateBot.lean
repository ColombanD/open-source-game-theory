import PrisonersDilemma.Program
import PrisonersDilemma.Dynamics
import PrisonersDilemma.Bots.LlmGenerations.LegibleBot
import PrisonersDilemma.Bots.CooperateBot
import PrisonersDilemma.Theorems.CooperateBot.Helpers
import PrisonersDilemma.Base.Helpers
import PrisonersDilemma.BaseTheorems
import PrisonersDilemma.Theorems.LegibleBot.Helpers

open PD
open PD.BaseTheorems
open PD.Bots
namespace PD.Theorems

/-- LegibleBot 2 2 vs CooperateBot: `(D, C)` — the floor-blind moralist of
    transparency EXPLOITS the unconditional cooperator: below the size floor it
    cannot certify its own legibility, so it defects on principle. -/
theorem outcome_LegibleBot_vs_CooperateBot (fuel : Nat) :
    outcome (fuel + 2) (LegibleBot 2 2) CooperateBot = some (.D, .C) :=
  outcome_of_plays _ _ _ _ _ (LegibleBot_defects_floor 2 2 fuel _ (by decide))
    (play_CooperateBot (fuel + 1) _)
end PD.Theorems
