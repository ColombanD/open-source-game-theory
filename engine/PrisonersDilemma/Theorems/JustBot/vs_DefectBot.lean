import PrisonersDilemma.Program
import PrisonersDilemma.Dynamics
import PrisonersDilemma.Bots.DupocBot
import PrisonersDilemma.Bots.CooperateBot
import PrisonersDilemma.Bots.DefectBot
import PrisonersDilemma.Bots.MirrorBot
import PrisonersDilemma.Bots.TitForTatBot
import PrisonersDilemma.Bots.LlmGenerations.JustBot
import PrisonersDilemma.Bots.LlmGenerations.PrudentBot
import PrisonersDilemma.Bots.CupodTrollBot
import PrisonersDilemma.Theorems.CooperateBot
import PrisonersDilemma.Theorems.DefectBot
import PrisonersDilemma.Theorems.DupocBot
import PrisonersDilemma.Base.Helpers
import PrisonersDilemma.Theorems.CupodTrollBot
import PrisonersDilemma.Theorems.PrudentBot.Helpers
import PrisonersDilemma.BaseTheorems
import PrisonersDilemma.Base.Asymptotics
import PrisonersDilemma.Theorems.JustBot.Helpers

open PD
open PD.BaseTheorems
open PD.Bots
namespace PD.Theorems

-- DefectBot --

/-- JustBot's substituted guard against DefectBot is false: DefectBot never plays C
    (against DupocBot or anything), so the guard search fails. -/
theorem proofSearch_false_for_JustBot_vs_DefectBot (k : Nat) :
    proofSearch k (Formula.plays DefectBot (.bot (DupocBot k)) Action.C) = false := by
  cases h : proofSearch k (Formula.plays DefectBot (.bot (DupocBot k)) Action.C) with
  | true  => exact absurd (proofSearch_sound _ _ h) (interp_DefectBot_plays_C_false _)
  | false => rfl

/-- JustBot defects against DefectBot: its guard fails. -/
theorem JustBot_plays_D_against_DefectBot (k fuel : Nat) :
    play (fuel + 2) (JustBot k) DefectBot = some .D := by
  refine JustBot_eval_step k fuel DefectBot .D ?_
  simpa using proofSearch_false_for_JustBot_vs_DefectBot k

/-- JustBot vs DefectBot: mutual defection. -/
theorem outcome_JustBot_vs_DefectBot (k fuel : Nat) :
    outcome (fuel + 2) (JustBot k) DefectBot = some (.D, .D) := by
  have hA : play (fuel + 2) (JustBot k) DefectBot = some .D :=
    JustBot_plays_D_against_DefectBot k fuel
  have hB : play (fuel + 2) DefectBot (JustBot k) = some .D := by
    simpa [Nat.add_comm] using play_DefectBot (fuel + 1) (JustBot k)
  exact outcome_of_plays _ _ _ _ _ hA hB
end PD.Theorems
