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
    RESOLVED (2026-07-30): the all-budget theorem below subsumes this floor
    (the `.neg`-guard Löb fixpoint closes via SP/WV valuation soundness). -/
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

/-- **WaryBot vs MirrorBot at ALL budgets: mutual cooperation.** Closes the
    `.neg`-guard Löb fixpoint that the floor theorem
    (`outcome_WaryBot_vs_MirrorBot_floor`, which this subsumes) left OPEN for
    large `k`: neither the refutation "¬(MirrorBot plays C vs WaryBot k)" nor
    any formula entailing it is derivable at ANY budget
    (`no_Pf_neg_mirror_wary`), so WaryBot's guard never fires and the mirror
    replays the trust. Proved by MODIFIED-VALUATION soundness
    (`WaryCensus.pf_WV_mirror`): a valuation making the fixpoint-entangled
    C-atoms (`WaryCensus.SPMirror`) true, under which every rule of `S` is
    sound and the refutation is false — NOT by a `TailTo` census, which is
    provably unusable for `.neg` tails (`contrapose ∘ implK` puts a provable
    member in any singleton `.neg`-tail class; do not retry that route). -/
theorem outcome_WaryBot_vs_MirrorBot (k fuel : Nat) :
    outcome (fuel + 3) (WaryBot k) MirrorBot = some (.C, .C) := by
  have hA : play (fuel + 3) (WaryBot k) MirrorBot = some .C := by
    simpa [Nat.add_assoc] using WaryBot_cooperates_vs_MirrorBot k (fuel + 1)
  exact outcome_of_plays _ _ _ _ _ hA (MirrorBot_plays_C_against_WaryBot k fuel)

end PD.Theorems
