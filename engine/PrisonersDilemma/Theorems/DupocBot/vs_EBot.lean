import PrisonersDilemma.Program
import PrisonersDilemma.Dynamics
import PrisonersDilemma.Bots.CooperateBot
import PrisonersDilemma.Bots.DupocBot
import PrisonersDilemma.Bots.EBot
import PrisonersDilemma.Theorems.CooperateBot.Helpers
import PrisonersDilemma.Theorems.DefectBot.Helpers
import PrisonersDilemma.Bots.DefectBot
import PrisonersDilemma.Base.Helpers
import PrisonersDilemma.BaseTheorems
import PrisonersDilemma.Base.Asymptotics
import PrisonersDilemma.Theorems.DupocBot.Helpers

open PD
open PD.BaseTheorems
open PD.Bots
namespace PD.Theorems
/-- **The honest DupocBot×EBot outcome — `(D, C)` for every `k ≥ 2`.** The simulator
    cooperates (its probes watched Dupoc defect on the DefectBot probe and cooperate on
    the CooperateBot probe), the searcher defects (the floor: EBot's cooperation
    certificate crosses Dupoc's own failed probe search). -/
theorem outcome_DupocBot_vs_EBot (k fuel : Nat) (hk : 2 ≤ k) :
    outcome (fuel + 5) (DupocBot k) EBot = some (.D, .C) := by
  have hA : play (fuel + 5) (DupocBot k) EBot = some .D := by
    simpa [Nat.add_assoc] using DupocBot_plays_D_against_EBot k (fuel + 3)
  have hB : play (fuel + 5) EBot (DupocBot k) = some .C :=
    EBot_plays_C_against_DupocBot k fuel
      (proofSearch_true_for_bot_CooperateBot_vs_Dupoc k hk)
  simp [outcome, hA, hB]

end PD.Theorems
