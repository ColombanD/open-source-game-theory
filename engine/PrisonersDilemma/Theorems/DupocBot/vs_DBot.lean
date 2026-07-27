import PrisonersDilemma.Program
import PrisonersDilemma.Dynamics
import PrisonersDilemma.Bots.CooperateBot
import PrisonersDilemma.Bots.DupocBot
import PrisonersDilemma.Bots.DBot
import PrisonersDilemma.Bots.OBot
import PrisonersDilemma.Bots.TitForTatBot
import PrisonersDilemma.Bots.EBot
import PrisonersDilemma.Bots.MirrorBot
import PrisonersDilemma.Theorems.CooperateBot.Helpers
import PrisonersDilemma.Theorems.CooperateBot.vs_CooperateBot
import PrisonersDilemma.Theorems.CooperateBot.vs_DefectBot
import PrisonersDilemma.Theorems.DefectBot.Helpers
import PrisonersDilemma.Theorems.DefectBot.vs_DefectBot
import PrisonersDilemma.Bots.DefectBot
import PrisonersDilemma.Base.Helpers
import PrisonersDilemma.BaseTheorems
import PrisonersDilemma.Base.Asymptotics
import PrisonersDilemma.Theorems.DupocBot.Helpers

open PD
open PD.BaseTheorems
open PD.Bots
namespace PD.Theorems
/-- **The honest DupocBot×DBot outcome — `(D, C)` at every budget.** The simulator
    cooperates (it watched Dupoc defect on the DefectBot probe), the searcher defects
    (it can never afford to certify a play that crosses its own failed search). -/
theorem outcome_DupocBot_vs_DBot (k fuel : Nat) :
    outcome (fuel + 4) (DupocBot k) DBot = some (.D, .C) := by
  have hA : play (fuel + 4) (DupocBot k) DBot = some .D := by
    simpa [Nat.add_assoc] using DupocBot_plays_D_against_DBot k (fuel + 2)
  have hB : play (fuel + 4) DBot (DupocBot k) = some .C :=
    DBot_plays_C_against_DupocBot k fuel
  simp [outcome, hA, hB]

end PD.Theorems
