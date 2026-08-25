import PrisonersDilemma.Program
import PrisonersDilemma.Dynamics
import PrisonersDilemma.Bots.DefectBot
import PrisonersDilemma.Bots.LlmGenerations.GuardianBot
import PrisonersDilemma.Theorems.DefectBot.Helpers
import PrisonersDilemma.Base.Helpers
import PrisonersDilemma.BaseTheorems
import PrisonersDilemma.Theorems.GuardianBot.Helpers
import PrisonersDilemma.Outcome

open PD
open PD.BaseTheorems
open PD.Bots
namespace PD.Theorems

/-- GuardianBot vs DefectBot: the norm enforcer punishes the provable bully.
    DefectBot's defection against the CooperateBot probe is a bare `.const`
    certificate, so the guard fires at every budget `k ≥ 1`. -/
@[outcome]
theorem outcome_GuardianBot_vs_DefectBot :
    OutcomeSpec .universal 2
      (fun k => GuardianBot (k + 1)) (fun _ => DefectBot) (some (.D, .D)) := by
  intro k fuel
  have hA : play (fuel + 2) (GuardianBot (k + 1)) DefectBot = some .D :=
    GuardianBot_defects_vs_DefectBot k fuel
  have hB : play (fuel + 2) DefectBot (GuardianBot (k + 1)) = some .D :=
    play_DefectBot (fuel + 1) _
  exact outcome_of_plays _ _ _ _ _ hA hB

end PD.Theorems
