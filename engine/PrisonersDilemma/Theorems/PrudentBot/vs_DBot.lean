import PrisonersDilemma.Program
import PrisonersDilemma.Dynamics
import PrisonersDilemma.Bots.DefectBot
import PrisonersDilemma.Bots.CooperateBot
import PrisonersDilemma.Bots.DBot
import PrisonersDilemma.Bots.OBot
import PrisonersDilemma.Bots.TitForTatBot
import PrisonersDilemma.BaseTheorems
import PrisonersDilemma.Bots.LlmGenerations.PrudentBot
import PrisonersDilemma.Theorems.CooperateBot
import PrisonersDilemma.Theorems.DefectBot
import PrisonersDilemma.Theorems.CupodTrollBot
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

-- DBot --

/-- DBot cooperates with PrudentBot: DBot probes PrudentBot against `.bot DefectBot`,
    sees it defect (guard value D ≠ test C), and takes its else-branch (cooperate). -/
theorem DBot_plays_C_vs_PrudentBot (k fuel : Nat) :
    play (fuel + 4) DBot (PrudentBot k) = some .C := by
  have hProbe : play (fuel + 2) (PrudentBot k) (.bot DefectBot) = some .D :=
    PrudentBot_plays_D_vs_bot_DB k fuel
  have hGuard : eval (fuel + 3) DBot (PrudentBot k) (.sim .opp (.bot DefectBot)) = some .D :=
    eval_sim_opp_bot_of_play (fuel + 2) DBot (PrudentBot k) DefectBot Action.D hProbe
  have hPlay := eval_ite_from_guard
    (fuel + 3) DBot (PrudentBot k) (.sim .opp (.bot DefectBot))
    (.const Action.D) (.const Action.C)
    Action.C Action.D
    hGuard
  show eval (fuel + 4) DBot (PrudentBot k) DBot = some .C
  rw [show DBot = .ite (.sim .opp (.bot DefectBot)) Action.C (.const Action.D) (.const Action.C) from rfl] at *
  rw [hPlay]; rfl

/-- The inner prudence search "DBot defects vs DefectBot" is false: DBot probes
    DefectBot (which defects), so DBot takes its else-branch and *cooperates*
    against DefectBot. Hence it is a sucker and the prudence atom is false. -/
theorem proofSearch_false_DBot_prudence (k : Nat) :
    proofSearch k (Formula.plays DBot (.bot DefectBot) Action.D) = false := by
  cases h : proofSearch k (Formula.plays DBot (.bot DefectBot) Action.D) with
  | true  =>
    exfalso
    obtain ⟨n, hn⟩ := proofSearch_sound _ _ h
    -- DBot cooperates vs `.bot DefectBot`, so it never plays D there.
    have hC : ∀ m, play (m + 4) DBot (.bot DefectBot) = some .C := by
      intro m
      have hProbe : play (m + 2) (.bot DefectBot) (.bot DefectBot) = some .D := by
        simpa [Nat.add_comm] using play_bot_DefectBot m (.bot DefectBot)
      have hGuard : eval (m + 3) DBot (.bot DefectBot) (.sim .opp (.bot DefectBot)) = some .D :=
        eval_sim_opp_bot_of_play (m + 2) DBot (.bot DefectBot) DefectBot Action.D hProbe
      have hPlay := eval_ite_from_guard
        (m + 3) DBot (.bot DefectBot) (.sim .opp (.bot DefectBot))
        (.const Action.D) (.const Action.C) Action.C Action.D hGuard
      show eval (m + 4) DBot (.bot DefectBot) DBot = some .C
      rw [show DBot = .ite (.sim .opp (.bot DefectBot)) Action.C (.const Action.D) (.const Action.C) from rfl] at *
      rw [hPlay]; rfl
    have hmono : play (n + 4) DBot (.bot DefectBot) = some .D := by
      unfold play at hn ⊢; exact eval_mono_le hn (n + 4) (by omega)
    rw [hC n] at hmono; cases hmono
  | false => rfl

/-- PrudentBot defects against DBot. Like CooperateBot, DBot cooperates with
    PrudentBot, but DBot is a sucker against DefectBot, so the inner prudence
    search fails and PrudentBot defects. -/
theorem PrudentBot_plays_D_against_DBot (k fuel : Nat) :
    play (fuel + 3) (PrudentBot k) DBot = some .D := by
  show eval (fuel + 3) (PrudentBot k) DBot (PrudentBot k) = some .D
  rw [PrudentBot_eq]
  show (if proofSearch k ((Formula.plays .opp .self Action.C).subst (PrudentBot k) DBot)
          then eval (fuel + 2) (PrudentBot k) DBot
                (.search k (Formula.plays .opp (.bot DefectBot) Action.D)
                  (.const Action.C) (.const Action.D))
          else eval (fuel + 2) (PrudentBot k) DBot (.const Action.D)) = some .D
  have hinner := proofSearch_false_DBot_prudence k
  by_cases hc : proofSearch k ((Formula.plays Prog.opp Prog.self Action.C).subst (PrudentBot k) DBot) = true
  · rw [if_pos hc]
    show (if proofSearch k ((Formula.plays .opp (.bot DefectBot) Action.D).subst (PrudentBot k) DBot)
            then eval (fuel + 1) (PrudentBot k) DBot (.const Action.C)
            else eval (fuel + 1) (PrudentBot k) DBot (.const Action.D)) = some .D
    rw [show (Formula.plays Prog.opp (.bot DefectBot) Action.D).subst (PrudentBot k) DBot
          = Formula.plays DBot (.bot DefectBot) Action.D from rfl, hinner]
    rfl
  · rw [if_neg hc]; rfl

/-- PrudentBot vs DBot: PrudentBot exploits, (D, C). -/
theorem outcome_PrudentBot_vs_DBot :
    ∃ k₂, ∀ k, k₂ < k →
      ∃ fuel, outcome fuel (PrudentBot k) DBot = some (.D, .C) := by
  refine ⟨0, fun k _ => ⟨7, ?_⟩⟩
  have hA : play 7 (PrudentBot k) DBot = some .D := by
    simpa using PrudentBot_plays_D_against_DBot k 4
  have hB : play 7 DBot (PrudentBot k) = some .C := by
    simpa using DBot_plays_C_vs_PrudentBot k 3
  exact outcome_of_plays _ _ _ _ _ hA hB
end PD.Theorems
