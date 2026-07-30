import PrisonersDilemma.Program
import PrisonersDilemma.Dynamics
import PrisonersDilemma.Bots.LlmGenerations.WaryBot
import PrisonersDilemma.Base.Helpers
import PrisonersDilemma.BaseTheorems
import PrisonersDilemma.Theorems.WaryBot.Helpers

open PD
open PD.BaseTheorems
open PD.Bots
namespace PD.Theorems

/-- WaryBot self-play, the whole FLOOR regime: neither copy can afford to
    refute the other's cooperation, so both trust — the refutation-side mirror
    of Löbian self-cooperation. RESOLVED (2026-07-30): the all-budget
    theorem below subsumes this floor (SP/WV valuation soundness). -/
theorem outcome_WaryBot_vs_WaryBot_floor (k fuel : Nat)
    (hsz : k < (Formula.neg (.plays (WaryBot k) (WaryBot k) .C)).size) :
    outcome (fuel + 2) (WaryBot k) (WaryBot k) = some (.C, .C) :=
  outcome_of_plays _ _ _ _ _ (WaryBot_cooperates_floor k fuel _ hsz)
    (WaryBot_cooperates_floor k fuel _ hsz)

/-- The concrete `k = 2` instance. -/
theorem outcome_WaryBot_vs_WaryBot_floor2 (fuel : Nat) :
    outcome (fuel + 2) (WaryBot 2) (WaryBot 2) = some (.C, .C) :=
  outcome_WaryBot_vs_WaryBot_floor 2 fuel (by decide)

/-- **WaryBot self-play at ALL budgets: mutual cooperation** — trust is the
    provable fixpoint. The refutation-guard analogue of Löbian self-cooperation
    resolves POSITIVELY: "¬(WaryBot k plays C vs itself)" is underivable at
    every budget (`no_Pf_neg_wary_self`, via `WaryCensus.pf_WV_self` — the
    self-play census whose base kill sits in the `search_t` arm, where the
    guard IS the excluded refutation), so both copies fall through to their
    trusting else-branches. Subsumes `outcome_WaryBot_vs_WaryBot_floor`; the
    `TailTo` route is falsified for `.neg` tails (see
    `outcome_WaryBot_vs_MirrorBot`). -/
theorem outcome_WaryBot_vs_WaryBot (k fuel : Nat) :
    outcome (fuel + 2) (WaryBot k) (WaryBot k) = some (.C, .C) :=
  outcome_of_plays _ _ _ _ _
    (WaryBot_cooperates_vs_WaryBot k fuel) (WaryBot_cooperates_vs_WaryBot k fuel)

end PD.Theorems
