import PrisonersDilemma.Program
import PrisonersDilemma.Dynamics
import PrisonersDilemma.Bots.CooperateBot
import PrisonersDilemma.Bots.CupodBot
import PrisonersDilemma.Bots.TitForTatBot
import PrisonersDilemma.Bots.DBot
import PrisonersDilemma.Bots.OBot
import PrisonersDilemma.Bots.EBot
import PrisonersDilemma.Bots.MirrorBot
import PrisonersDilemma.Theorems.CooperateBot
import PrisonersDilemma.Theorems.DefectBot
import PrisonersDilemma.Bots.DefectBot
import PrisonersDilemma.Base.Helpers
import PrisonersDilemma.BaseTheorems
import PrisonersDilemma.Base.Asymptotics
import PrisonersDilemma.Theorems.CupodBot.Helpers

open PD
open PD.Bots
open PD.BaseTheorems
namespace PD.Theorems
/-- **The honest CupodBot×OBot outcome — `(C, D)` for every `k ≥ 2`.** The trusting
    searcher gets exploited: OBot's real defection is uncertifiable within Cupod's own
    budget (the floor), so Cupod cooperates into the sucker payoff. -/
theorem outcome_CupodBot_vs_OBot (k fuel : Nat) (hk : 2 ≤ k) :
    outcome (fuel + 5) (CupodBot k) OBot = some (.C, .D) := by
  have hA : play (fuel + 5) (CupodBot k) OBot = some .C := by
    simpa [Nat.add_assoc] using CupodBot_plays_C_against_OBot k (fuel + 3)
  have hB : play (fuel + 5) OBot (CupodBot k) = some .D :=
    OBot_plays_D_against_CupodBot k fuel (proofSearch_true_for_bot_DefectBot_vs_Cupod k hk)
  simp [outcome, hA, hB]

end PD.Theorems
