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

open PD
open PD.BaseTheorems
open PD.Bots
namespace PD.Theorems

/-! # PrudentBot — shared lemmas used across the `vs_*` files.
Split from `LlmGenerations/PrudentBot.lean` (per-pair refactor, 2026-07-27):
the head/else-branch core, the canonical probe responses (`.bot DefectBot`,
`.bot CooperateBot`), and the generic guard-driven eval/inversion lemmas
(also consumed by `Theorems/JustBot/vs_PrudentBot.lean`). -/

/-- PrudentBot's head, unfolded once. The cooperation `.search` is at the root;
    the prudence (`opp defects vs DefectBot`) search is folded into its THEN
    branch. -/
theorem PrudentBot_eq (k : Nat) :
    PrudentBot k = .search k (Formula.plays .opp .self Action.C)
      (.search k (Formula.plays .opp (.bot DefectBot) Action.D)
        (.const Action.C) (.const Action.D))
      (.const Action.D) := rfl


/-- Core lemma for every matchup in which PrudentBot defects: if the opponent
    `opp` does **not** cooperate with PrudentBot (the outer cooperation search is
    false), PrudentBot lands in the root `.search`'s else-branch and defects. The
    inner prudence search is never reached. -/
theorem PrudentBot_plays_D_of_search_false (k fuel : Nat) (opponent : Prog)
    (hf : proofSearch k (Formula.plays opponent (PrudentBot k) Action.C) = false) :
    play (fuel + 2) (PrudentBot k) opponent = some .D := by
  show eval (fuel + 2) (PrudentBot k) opponent (PrudentBot k) = some .D
  rw [PrudentBot_eq]
  show (if proofSearch k ((Formula.plays .opp .self Action.C).subst (PrudentBot k) opponent)
          then eval (fuel + 1) (PrudentBot k) opponent
                (.search k (Formula.plays .opp (.bot DefectBot) Action.D)
                  (.const Action.C) (.const Action.D))
          else eval (fuel + 1) (PrudentBot k) opponent (.const Action.D)) = some .D
  rw [show (Formula.plays Prog.opp Prog.self Action.C).subst (PrudentBot k) opponent
        = Formula.plays opponent (PrudentBot k) Action.C from rfl, hf]
  rfl
-- Probe lemmas: how PrudentBot responds to the canonical probe bots that
-- DBot/OBot/TFT simulate it against.

/-- PrudentBot defects against `.bot DefectBot`: the outer cooperation search
    "DefectBot cooperates with PrudentBot" is false. -/
theorem PrudentBot_plays_D_vs_bot_DB (k fuel : Nat) :
    play (fuel + 2) (PrudentBot k) (.bot DefectBot) = some .D := by
  apply PrudentBot_plays_D_of_search_false
  cases h : proofSearch k (Formula.plays (.bot DefectBot) (PrudentBot k) Action.C) with
  | true  => exact absurd (proofSearch_sound _ _ h) (interp_bot_DefectBot_plays_C_false _)
  | false => rfl

/-- PrudentBot defects against `.bot CooperateBot`: outer cooperation search may
    succeed, but the inner prudence search ("CooperateBot defects vs DefectBot")
    fails, so PrudentBot defects. -/
theorem PrudentBot_plays_D_vs_bot_CB (k fuel : Nat) :
    play (fuel + 3) (PrudentBot k) (.bot CooperateBot) = some .D := by
  show eval (fuel + 3) (PrudentBot k) (.bot CooperateBot) (PrudentBot k) = some .D
  rw [PrudentBot_eq]
  show (if proofSearch k ((Formula.plays .opp .self Action.C).subst (PrudentBot k) (.bot CooperateBot))
          then eval (fuel + 2) (PrudentBot k) (.bot CooperateBot)
                (.search k (Formula.plays .opp (.bot DefectBot) Action.D)
                  (.const Action.C) (.const Action.D))
          else eval (fuel + 2) (PrudentBot k) (.bot CooperateBot) (.const Action.D)) = some .D
  have hinner : proofSearch k (Formula.plays (.bot CooperateBot) (.bot DefectBot) Action.D) = false := by
    cases h : proofSearch k (Formula.plays (.bot CooperateBot) (.bot DefectBot) Action.D) with
    | true  =>
      exfalso
      obtain ⟨n, hn⟩ := proofSearch_sound _ _ h
      cases n with
      | zero   => simp [play, eval] at hn
      | succ m =>
          cases m with
          | zero => simp [play, eval] at hn
          | succ j =>
              rw [show play (j+2) (.bot CooperateBot) (.bot DefectBot) = some .C from by
                    simp [play, eval, CooperateBot]] at hn
              cases hn
    | false => rfl
  by_cases hc : proofSearch k ((Formula.plays Prog.opp Prog.self Action.C).subst (PrudentBot k) (.bot CooperateBot)) = true
  · rw [if_pos hc]
    show (if proofSearch k ((Formula.plays .opp (.bot DefectBot) Action.D).subst (PrudentBot k) (.bot CooperateBot))
            then eval (fuel + 1) (PrudentBot k) (.bot CooperateBot) (.const Action.C)
            else eval (fuel + 1) (PrudentBot k) (.bot CooperateBot) (.const Action.D)) = some .D
    rw [show (Formula.plays Prog.opp (.bot DefectBot) Action.D).subst (PrudentBot k) (.bot CooperateBot)
          = Formula.plays (.bot CooperateBot) (.bot DefectBot) Action.D from rfl, hinner]
    rfl
  · rw [if_neg hc]; rfl
/-- PrudentBot defects when its outer search guard fails. -/
theorem prudent_eval_outer_false (k fuel : Nat) (q : Prog)
    (h1 : proofSearch k (.plays q (PrudentBot k) .C) = false) :
    play (fuel + 2) (PrudentBot k) q = some .D := by
  show eval (fuel + 2) (PrudentBot k) q (PrudentBot k) = some .D
  unfold PrudentBot at h1 ⊢
  simp [eval, Prog.subst, Formula.subst, h1]

/-- PrudentBot defects when outer guard holds but inner (prudence) guard fails. -/
theorem prudent_eval_inner_false (k fuel : Nat) (q : Prog)
    (h1 : proofSearch k (.plays q (PrudentBot k) .C) = true)
    (h2 : proofSearch k (.plays q (.bot DefectBot) .D) = false) :
    play (fuel + 3) (PrudentBot k) q = some .D := by
  show eval (fuel + 3) (PrudentBot k) q (PrudentBot k) = some .D
  unfold PrudentBot at h1 ⊢
  simp [eval, Prog.subst, Formula.subst, h1, h2]

/-- PrudentBot cooperates when both guards hold. -/
theorem prudent_eval_both_true (k fuel : Nat) (q : Prog)
    (h1 : proofSearch k (.plays q (PrudentBot k) .C) = true)
    (h2 : proofSearch k (.plays q (.bot DefectBot) .D) = true) :
    play (fuel + 3) (PrudentBot k) q = some .C := by
  show eval (fuel + 3) (PrudentBot k) q (PrudentBot k) = some .C
  unfold PrudentBot at h1 ⊢
  simp [eval, Prog.subst, Formula.subst, h1, h2]

/-- Inversion: if PrudentBot plays C against q, its outer guard fired. -/
theorem prudent_outer_true_of_play_C (k n : Nat) (q : Prog)
    (h : play n (PrudentBot k) q = some .C) :
    proofSearch k (.plays q (PrudentBot k) .C) = true := by
  cases hps : proofSearch k (.plays q (PrudentBot k) .C) with
  | true => rfl
  | false =>
    exfalso
    rcases n with _ | _ | n
    · simp [play, eval] at h
    · simp [play, eval, PrudentBot, Prog.subst, Formula.subst] at h
    · have hD : play (n + 2) (PrudentBot k) q = some .D :=
        prudent_eval_outer_false k n q hps
      rw [hD] at h; cases h
end PD.Theorems
