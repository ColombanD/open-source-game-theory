import PrisonersDilemma.Bots.CupodBot
import PrisonersDilemma.Bots.TitForTatBot
import PrisonersDilemma.Bots.CooperateBot
import PrisonersDilemma.Axioms
import PrisonersDilemma.Theorems.Helpers
import PrisonersDilemma.Theorems.ProofSearch

open PDNew
open PDNew.Bots
open PDNew.Axioms

namespace PDNew.Theorems

theorem llm_outcome_CupodBot_vs_TitForTatBot (n k : Nat) :
    outcome (n+5) (CupodBot k) TitForTatBot = some (.C, .C) := by
  -- L1: (.bot CooperateBot) never plays D against (CupodBot k)
  have hL1 : ∀ m, play m (.bot CooperateBot) (CupodBot k) ≠ some .D := by
    intro m h
    cases m with
    | zero => simp [play, eval] at h
    | succ m' =>
      cases m' with
      | zero => simp [play, eval] at h
      | succ m'' => simp [play, eval, CooperateBot] at h
  -- L2: proofSearch for "(.bot CB) plays D vs CupodBot" is false
  have hPS1 : proofSearch k (.plays (.bot CooperateBot) (CupodBot k) .D) = false := by
    cases hh : proofSearch k (.plays (.bot CooperateBot) (CupodBot k) .D) with
    | false => rfl
    | true =>
      exfalso
      obtain ⟨nn, hnn⟩ := proofSearch_sound _ _ hh
      exact hL1 nn hnn
  -- Helper for one-step eval of CupodBot
  have hCupodStep : ∀ m (opponent : Prog),
    eval (m+1) (CupodBot k) opponent (CupodBot k)
    = (if proofSearch k (Formula.plays opponent (CupodBot k) .D)
       then eval m (CupodBot k) opponent (.const .D)
       else eval m (CupodBot k) opponent (.const .C)) := by
    intro m opponent
    rfl
  -- L3: CupodBot vs (.bot CooperateBot) never plays D
  have hL3 : ∀ m, play m (CupodBot k) (.bot CooperateBot) ≠ some .D := by
    intro m h
    cases m with
    | zero => simp [play, eval] at h
    | succ m' =>
      have hstep : play (m'+1) (CupodBot k) (.bot CooperateBot)
                 = eval m' (CupodBot k) (.bot CooperateBot) (.const .C) := by
        show eval (m'+1) (CupodBot k) (.bot CooperateBot) (CupodBot k) = _
        rw [hCupodStep m' (.bot CooperateBot), hPS1]
        rfl
      rw [hstep] at h
      cases m' with
      | zero => simp [eval] at h
      | succ _ => simp [eval] at h
  -- L4: TFT vs CupodBot never plays D
  have hL4 : ∀ m, play m TitForTatBot (CupodBot k) ≠ some .D := by
    intro m h
    cases m with
    | zero => simp [play, eval] at h
    | succ m' =>
      cases m' with
      | zero => simp [play, eval, TitForTatBot] at h
      | succ m'' =>
        have hguard_eq :
          eval (m''+1) TitForTatBot (CupodBot k) (.sim .opp (.bot CooperateBot))
          = play m'' (CupodBot k) (.bot CooperateBot) := rfl
        cases hg : play m'' (CupodBot k) (.bot CooperateBot) with
        | none =>
          have hplay_none : play (m''+2) TitForTatBot (CupodBot k) = none := by
            show eval (m''+2) TitForTatBot (CupodBot k) TitForTatBot = none
            show (do let r ← eval (m''+1) TitForTatBot (CupodBot k) (.sim .opp (.bot CooperateBot))
                     if r == .C then eval (m''+1) TitForTatBot (CupodBot k) (.const .C)
                     else eval (m''+1) TitForTatBot (CupodBot k) (.const .D)) = none
            rw [hguard_eq, hg]
            rfl
          rw [hplay_none] at h
          exact absurd h (by decide)
        | some r =>
          cases r with
          | C =>
            have hgvC : eval (m''+1) TitForTatBot (CupodBot k) (.sim .opp (.bot CooperateBot)) = some .C := by
              rw [hguard_eq]; exact hg
            have hP : play (m''+1+1) TitForTatBot (CupodBot k) = some .C :=
              play_ite_from_guard m'' 1 TitForTatBot (CupodBot k)
                (.sim .opp (.bot CooperateBot)) (.const .C) (.const .D) .C .C
                rfl hgvC
            exact absurd (hP.symm.trans h) (by decide)
          | D => exact hL3 m'' hg
  -- L5: proofSearch for "TFT plays D vs CupodBot" is false
  have hPS2 : proofSearch k (.plays TitForTatBot (CupodBot k) .D) = false := by
    cases hh : proofSearch k (.plays TitForTatBot (CupodBot k) .D) with
    | false => rfl
    | true =>
      exfalso
      obtain ⟨nn, hnn⟩ := proofSearch_sound _ _ hh
      exact hL4 nn hnn
  -- Compute outcome
  have hA : play (n+5) (CupodBot k) TitForTatBot = some .C := by
    show eval (n+5) (CupodBot k) TitForTatBot (CupodBot k) = some .C
    rw [hCupodStep (n+4) TitForTatBot, hPS2]
    rfl
  have hB : play (n+5) TitForTatBot (CupodBot k) = some .C := by
    have hg_inner : play (n+3) (CupodBot k) (.bot CooperateBot) = some .C := by
      show eval (n+3) (CupodBot k) (.bot CooperateBot) (CupodBot k) = some .C
      rw [hCupodStep (n+2) (.bot CooperateBot), hPS1]
      rfl
    have hgEval : eval (n+4) TitForTatBot (CupodBot k) (.sim .opp (.bot CooperateBot)) = some .C :=
      eval_sim_opp_bot_of_play (n+3) TitForTatBot (CupodBot k) CooperateBot .C hg_inner
    have hP := play_ite_from_guard
        n 4 TitForTatBot (CupodBot k)
        (.sim .opp (.bot CooperateBot))
        (.const .C) (.const .D)
        .C .C
        rfl hgEval
    exact hP
  exact outcome_of_plays _ _ _ _ _ hA hB

end PDNew.Theorems
