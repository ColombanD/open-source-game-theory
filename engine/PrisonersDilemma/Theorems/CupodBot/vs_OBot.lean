import PrisonersDilemma.Program
import PrisonersDilemma.Dynamics
import PrisonersDilemma.Bots.CupodBot
import PrisonersDilemma.Bots.OBot
import PrisonersDilemma.Base.Helpers
import PrisonersDilemma.BaseTheorems
import PrisonersDilemma.Base.Asymptotics
import PrisonersDilemma.Theorems.CupodBot.Helpers
import PrisonersDilemma.Outcome

open PD
open PD.Bots
open PD.BaseTheorems
namespace PD.Theorems
/-- **The honest CupodBot×OBot outcome — `(C, D)` for every `k ≥ 2`.** The trusting
    searcher gets exploited: OBot's real defection is uncertifiable within Cupod's own
    budget (the floor), so Cupod cooperates into the sucker payoff.

    Stated in the `.eventual` regime: the old `(hk : 2 ≤ k)` binder was never a caveat
    on the RESULT, only a minimum budget for OBot's guard to fire at all — which is
    exactly what "at every sufficiently large `k`" means. Expressing it as the regime
    rather than a side condition is why this cell no longer carries a dagger. -/
@[outcome]
theorem outcome_CupodBot_vs_OBot :
    OutcomeSpec .eventual 5 CupodBot (fun _ => OBot) (some (.C, .D)) := by
  refine ⟨1, fun k hlt fuel => ?_⟩
  have hk : 2 ≤ k := hlt
  have hA : play (fuel + 5) (CupodBot k) OBot = some .C := by
    simpa [Nat.add_assoc] using CupodBot_plays_C_against_OBot k (fuel + 3)
  have hB : play (fuel + 5) OBot (CupodBot k) = some .D :=
    OBot_plays_D_against_CupodBot k fuel (proofSearch_true_for_bot_DefectBot_vs_Cupod k hk)
  simp [outcome, hA, hB]

end PD.Theorems
