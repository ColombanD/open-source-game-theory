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

-- CooperateBot --

/-- The inner prudence search "CooperateBot defects vs DefectBot" is false:
    CooperateBot cooperates against everything, so it never plays D. -/
theorem proofSearch_false_CooperateBot_prudence (k : Nat) :
    proofSearch k (Formula.plays CooperateBot (.bot DefectBot) Action.D) = false := by
  cases h : proofSearch k (Formula.plays CooperateBot (.bot DefectBot) Action.D) with
  | true  =>
    exfalso
    obtain ⟨n, hn⟩ := proofSearch_sound _ _ h
    cases n with
    | zero   => simp [play, eval] at hn
    | succ m =>
        rw [show play (m+1) CooperateBot (.bot DefectBot) = some .C from by
              simpa [Nat.add_comm] using play_CooperateBot m (.bot DefectBot)] at hn
        cases hn
  | false => rfl

/-- PrudentBot defects against CooperateBot. The outer cooperation search may
    succeed (CooperateBot does cooperate), but then the inner *prudence* search
    fails (CooperateBot is a sucker — it cooperates vs DefectBot), so PrudentBot
    defects via the inner else-branch. Either way: defect. -/
theorem PrudentBot_plays_D_against_CooperateBot (k fuel : Nat) :
    play (fuel + 3) (PrudentBot k) CooperateBot = some .D := by
  show eval (fuel + 3) (PrudentBot k) CooperateBot (PrudentBot k) = some .D
  rw [PrudentBot_eq]
  show (if proofSearch k ((Formula.plays .opp .self Action.C).subst (PrudentBot k) CooperateBot)
          then eval (fuel + 2) (PrudentBot k) CooperateBot
                (.search k (Formula.plays .opp (.bot DefectBot) Action.D)
                  (.const Action.C) (.const Action.D))
          else eval (fuel + 2) (PrudentBot k) CooperateBot (.const Action.D)) = some .D
  have hinner := proofSearch_false_CooperateBot_prudence k
  by_cases hc : proofSearch k ((Formula.plays Prog.opp Prog.self Action.C).subst (PrudentBot k) CooperateBot) = true
  · rw [if_pos hc]
    show (if proofSearch k ((Formula.plays .opp (.bot DefectBot) Action.D).subst (PrudentBot k) CooperateBot)
            then eval (fuel + 1) (PrudentBot k) CooperateBot (.const Action.C)
            else eval (fuel + 1) (PrudentBot k) CooperateBot (.const Action.D)) = some .D
    rw [show (Formula.plays Prog.opp (.bot DefectBot) Action.D).subst (PrudentBot k) CooperateBot
          = Formula.plays CooperateBot (.bot DefectBot) Action.D from rfl, hinner]
    rfl
  · rw [if_neg hc]; rfl

/-- PrudentBot vs CooperateBot: PrudentBot exploits the sucker, (D, C). -/
theorem outcome_PrudentBot_vs_CooperateBot (k fuel : Nat) :
    outcome (fuel + 3) (PrudentBot k) CooperateBot = some (.D, .C) := by
  have hA : play (fuel + 3) (PrudentBot k) CooperateBot = some .D :=
    PrudentBot_plays_D_against_CooperateBot k fuel
  have hB : play (fuel + 3) CooperateBot (PrudentBot k) = some .C := by
    simpa [Nat.add_comm] using play_CooperateBot (fuel + 2) (PrudentBot k)
  exact outcome_of_plays _ _ _ _ _ hA hB
end PD.Theorems
