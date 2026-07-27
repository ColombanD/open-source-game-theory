import PrisonersDilemma.Program
import PrisonersDilemma.Dynamics
import PrisonersDilemma.Bots.DefectBot
import PrisonersDilemma.Bots.CooperateBot
import PrisonersDilemma.Bots.DBot
import PrisonersDilemma.Bots.OBot
import PrisonersDilemma.Bots.TitForTatBot
import PrisonersDilemma.BaseTheorems
import PrisonersDilemma.Bots.LlmGenerations.PrudentBot
import PrisonersDilemma.Theorems.CooperateBot.Helpers
import PrisonersDilemma.Theorems.CooperateBot.vs_CooperateBot
import PrisonersDilemma.Theorems.CooperateBot.vs_DefectBot
import PrisonersDilemma.Theorems.DefectBot.Helpers
import PrisonersDilemma.Theorems.DefectBot.vs_DefectBot
import PrisonersDilemma.Theorems.CupodTrollBot.Helpers
import PrisonersDilemma.Theorems.CupodTrollBot.vs_CooperateBot
import PrisonersDilemma.Theorems.CupodTrollBot.vs_CupodBot
import PrisonersDilemma.Theorems.CupodTrollBot.vs_CupodTrollBot
import PrisonersDilemma.Theorems.CupodTrollBot.vs_DBot
import PrisonersDilemma.Theorems.CupodTrollBot.vs_DefectBot
import PrisonersDilemma.Theorems.CupodTrollBot.vs_DupocBot
import PrisonersDilemma.Theorems.CupodTrollBot.vs_EBot
import PrisonersDilemma.Theorems.CupodTrollBot.vs_MirrorBot
import PrisonersDilemma.Theorems.CupodTrollBot.vs_OBot
import PrisonersDilemma.Theorems.CupodTrollBot.vs_TitForTatBot
import PrisonersDilemma.Base.Helpers
import PrisonersDilemma.BaseTheorems
import PrisonersDilemma.Base.Asymptotics
import PrisonersDilemma.Bots.EBot
import PrisonersDilemma.Bots.CupodTrollBot
import PrisonersDilemma.Theorems.PrudentBot.Helpers

open PD
open PD.BaseTheorems
open PD.Bots
namespace PD.Theorems

-- DefectBot --

/-- The outer cooperation search "DefectBot cooperates with PrudentBot" is false:
    DefectBot never plays C. -/
theorem proofSearch_false_DefectBot_vs_PrudentBot (k : Nat) :
    proofSearch k (Formula.plays DefectBot (PrudentBot k) Action.C) = false := by
  cases h : proofSearch k (Formula.plays DefectBot (PrudentBot k) Action.C) with
  | true  => exact absurd (proofSearch_sound _ _ h) (interp_DefectBot_plays_C_false _)
  | false => rfl

/-- PrudentBot defects against DefectBot (outer cooperation search fails). -/
theorem PrudentBot_plays_D_against_DefectBot (k fuel : Nat) :
    play (fuel + 2) (PrudentBot k) DefectBot = some .D :=
  PrudentBot_plays_D_of_search_false k fuel DefectBot
    (proofSearch_false_DefectBot_vs_PrudentBot k)

/-- PrudentBot vs DefectBot: mutual defection, (D, D). -/
theorem outcome_PrudentBot_vs_DefectBot (k fuel : Nat) :
    outcome (fuel + 2) (PrudentBot k) DefectBot = some (.D, .D) := by
  have hA : play (fuel + 2) (PrudentBot k) DefectBot = some .D :=
    PrudentBot_plays_D_against_DefectBot k fuel
  have hB : play (fuel + 2) DefectBot (PrudentBot k) = some .D := by
    simpa [Nat.add_comm] using play_DefectBot (fuel + 1) (PrudentBot k)
  exact outcome_of_plays _ _ _ _ _ hA hB
end PD.Theorems
