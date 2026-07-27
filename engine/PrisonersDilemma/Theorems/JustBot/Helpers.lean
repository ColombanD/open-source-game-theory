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

open PD
open PD.BaseTheorems
open PD.Bots
namespace PD.Theorems

/-! # JustBot — shared play/guard lemmas used by several `vs_*` files.
Split from `LlmGenerations/JustBot.lean` (per-pair refactor, 2026-07-27). -/

/-- One evaluation step of JustBot: it consults its guard `proofSearch` and takes
    the corresponding constant branch (cooperate iff the guard fires). -/
theorem JustBot_eval_step (k fuel : Nat) (X : Prog) (a : Action)
    (hg : proofSearch k (Formula.plays X (.bot (DupocBot k)) Action.C)
            = (a == Action.C)) :
    play (fuel + 2) (JustBot k) X = some a := by
  -- The guard `proofSearch` argument is definitionally `.plays X (.bot (DupocBot k)) .C`.
  show (if proofSearch k (Formula.plays X (.bot (DupocBot k)) Action.C)
          then eval (fuel + 1) (JustBot k) X (.const Action.C)
          else eval (fuel + 1) (JustBot k) X (.const Action.D)) = some a
  rw [hg]
  cases a with
  | C => simp [eval]; rfl
  | D => simp [eval]; rfl
-- .bot DefectBot cannot play C against anything
theorem ps_false_bot_DefectBot_vs_bot_DupocBot_JB (k : Nat) :
    proofSearch k (.plays (.bot DefectBot) (.bot (DupocBot k)) .C) = false := by
  cases h : proofSearch k (.plays (.bot DefectBot) (.bot (DupocBot k)) .C) with
  | true =>
    exact absurd (proofSearch_sound _ _ h) (by
      rintro ⟨n, hn⟩
      rcases n with _ | _ | n
      · simp [play, eval] at hn
      · simp [play, eval] at hn
      · simp [play, eval, DefectBot] at hn)
  | false => rfl
-- JustBot k defects against .bot DefectBot: its guard (.plays .bot DefectBot ...) fails
theorem JustBot_plays_D_against_bot_DefectBot_JB (k fuel : Nat) :
    play (fuel + 2) (JustBot k) (.bot DefectBot) = some .D := by
  have hg := ps_false_bot_DefectBot_vs_bot_DupocBot_JB k
  show eval (fuel + 2) (JustBot k) (.bot DefectBot) (JustBot k) = some .D
  unfold JustBot
  simp [eval, Prog.subst, Formula.subst, hg]
/-- JustBot's guard against `.bot CooperateBot` is the *same* shared formula
    `.plays (.bot CooperateBot) (.bot (DupocBot k)) .C`, so JustBot cooperates
    against `.bot CooperateBot` whenever the shared guard fires. This is what makes
    TFT (which probes its opponent against `.bot CooperateBot`) cooperate with
    JustBot. -/
theorem JustBot_plays_C_against_bot_CooperateBot (k fuel : Nat)
    (hk : proofSearch k (Formula.plays (.bot CooperateBot) (.bot (DupocBot k)) Action.C) = true) :
    play (fuel + 2) (JustBot k) (.bot CooperateBot) = some .C := by
  refine JustBot_eval_step k fuel (.bot CooperateBot) .C ?_
  simpa using hk
end PD.Theorems
