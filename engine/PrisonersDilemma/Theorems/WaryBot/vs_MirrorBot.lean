import PrisonersDilemma.Program
import PrisonersDilemma.Dynamics
import PrisonersDilemma.Bots.LlmGenerations.WaryBot
import PrisonersDilemma.Bots.MirrorBot
import PrisonersDilemma.Base.Helpers
import PrisonersDilemma.BaseTheorems
import PrisonersDilemma.Theorems.WaryBot.Helpers

open PD
open PD.BaseTheorems
open PD.Bots
namespace PD.Theorems

/-- WaryBot vs MirrorBot, the whole FLOOR regime: at every budget below the
    guard size the mirror replays the floor-forced trust — mutual cooperation.
    The large-`k` outcome is OPEN: it is the `.neg`-guard Löb fixpoint (no
    `diag` analogue for refutation guards exists yet). -/
theorem outcome_WaryBot_vs_MirrorBot_floor (k fuel : Nat)
    (hsz : k < (Formula.neg (.plays MirrorBot (WaryBot k) .C)).size) :
    outcome (fuel + 3) (WaryBot k) MirrorBot = some (.C, .C) := by
  have hA : play (fuel + 3) (WaryBot k) MirrorBot = some .C := by
    simpa [Nat.add_assoc] using WaryBot_cooperates_floor k (fuel + 1) MirrorBot hsz
  exact outcome_of_plays _ _ _ _ _ hA
    (MirrorBot_plays_C_against_WaryBot_floor k fuel hsz)

/-- The concrete `k = 2` instance. -/
theorem outcome_WaryBot_vs_MirrorBot_floor2 (fuel : Nat) :
    outcome (fuel + 3) (WaryBot 2) MirrorBot = some (.C, .C) :=
  outcome_WaryBot_vs_MirrorBot_floor 2 fuel (by decide)
end PD.Theorems
