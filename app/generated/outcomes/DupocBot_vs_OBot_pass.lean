import PrisonersDilemma.Bots.DupocBot
import PrisonersDilemma.Bots.OBot
import PrisonersDilemma.Bots.CooperateBot
import PrisonersDilemma.Bots.DefectBot
import PrisonersDilemma.Axioms
import PrisonersDilemma.Theorems.Helpers
import PrisonersDilemma.Theorems.ProofSearch

open PD
open PD.Axioms
open PD.Bots
namespace PD.Theorems

theorem interp_bot_DefectBot_plays_C_false_dupoc (k : Nat) :
    ¬ (Formula.plays (.bot DefectBot) (DupocBot k) .C).interp := by
  rintro ⟨n, hn⟩
  cases n with
  | zero => simp [play, eval] at hn
  | succ m =>
    cases m with
    | zero => simp [play, eval] at hn
    | succ m' => simp [play, eval, DefectBot] at hn

theorem proofSearch_false_DefectBot_C_dupoc (k : Nat) :
    proofSearch k (.plays (.bot DefectBot) (DupocBot k) .C) = false := by
  cases h : proofSearch k (.plays (.bot DefectBot) (DupocBot k) .C) with
  | true => exact absurd (proofSearch_sound _ _ h) (interp_bot_DefectBot_plays_C_false_dupoc k)
  | false => rfl

theorem DupocBot_plays_D_against_bot_DefectBot (k fuel : Nat) :
    play (fuel + 2) (DupocBot k) (.bot DefectBot) = some .D := by
  have hg := proofSearch_false_DefectBot_C_dupoc k
  show eval (fuel + 2) (DupocBot k) (.bot DefectBot) (DupocBot k) = some .D
  unfold DupocBot at hg ⊢
  simp [eval, Prog.subst, Formula.subst, hg]

theorem OBot_plays_D_against_DupocBot (k fuel : Nat) :
    play (fuel + 6) OBot (DupocBot k) = some .D := by
  have hInnerProbe : play (fuel + 2) (DupocBot k) (.bot DefectBot) = some .D :=
    DupocBot_plays_D_against_bot_DefectBot k fuel
  have hGuard2 : eval (fuel + 3) OBot (DupocBot k) (.sim .opp (.bot DefectBot)) = some .D :=
    eval_sim_opp_bot_of_play _ _ _ _ _ hInnerProbe
  by_cases hCB : proofSearch k (.plays (.bot CooperateBot) (DupocBot k) .C) = true
  · have hOuterProbe : play (fuel + 3) (DupocBot k) (.bot CooperateBot) = some .C := by
      show eval (fuel + 3) (DupocBot k) (.bot CooperateBot) (DupocBot k) = some .C
      unfold DupocBot at hCB ⊢
      simp [eval, Prog.subst, Formula.subst, hCB]
    have hGuard1 : eval (fuel + 4) OBot (DupocBot k) (.sim .opp (.bot CooperateBot)) = some .C :=
      eval_sim_opp_bot_of_play _ _ _ _ _ hOuterProbe
    have hInnerIte :
        eval (fuel + 4) OBot (DupocBot k)
          (.ite (.sim .opp (.bot DefectBot)) .C (.const .C) (.const .D)) = some .D := by
      have h := eval_ite_from_guard (fuel + 3) OBot (DupocBot k)
        (.sim .opp (.bot DefectBot)) (.const .C) (.const .D) .C .D hGuard2
      simpa using h
    have hPlay := play_ite_from_guard fuel 4 OBot (DupocBot k)
      (.sim .opp (.bot CooperateBot))
      (.ite (.sim .opp (.bot DefectBot)) .C (.const .C) (.const .D))
      (.const .D)
      .C .C
      (by rfl) hGuard1
    simpa [hInnerIte] using hPlay
  · have hCBFalse : proofSearch k (.plays (.bot CooperateBot) (DupocBot k) .C) = false := by
      cases h : proofSearch k (.plays (.bot CooperateBot) (DupocBot k) .C) with
      | true => exact absurd h hCB
      | false => rfl
    have hOuterProbe : play (fuel + 3) (DupocBot k) (.bot CooperateBot) = some .D := by
      show eval (fuel + 3) (DupocBot k) (.bot CooperateBot) (DupocBot k) = some .D
      unfold DupocBot at hCBFalse ⊢
      simp [eval, Prog.subst, Formula.subst, hCBFalse]
    have hGuard1 : eval (fuel + 4) OBot (DupocBot k) (.sim .opp (.bot CooperateBot)) = some .D :=
      eval_sim_opp_bot_of_play _ _ _ _ _ hOuterProbe
    have hPlay := play_ite_from_guard fuel 4 OBot (DupocBot k)
      (.sim .opp (.bot CooperateBot))
      (.ite (.sim .opp (.bot DefectBot)) .C (.const .C) (.const .D))
      (.const .D)
      .C .D
      (by rfl) hGuard1
    simpa [eval] using hPlay

theorem interp_OBot_plays_C_false_dupoc (k : Nat) :
    ¬ (Formula.plays OBot (DupocBot k) .C).interp := by
  rintro ⟨n, hn⟩
  have hDFalse := proofSearch_false_DefectBot_C_dupoc k
  unfold DupocBot at hDFalse
  have hDC : (Action.D == Action.C) = false := rfl
  cases n with
  | zero => simp [play, eval] at hn
  | succ m =>
  cases m with
  | zero => simp [play, eval, OBot] at hn
  | succ m =>
  cases m with
  | zero => simp [play, eval, OBot] at hn
  | succ m =>
  cases m with
  | zero =>
    unfold OBot DupocBot at hn
    simp [play, eval, Prog.subst, Formula.subst] at hn
  | succ m =>
  cases m with
  | zero =>
    by_cases hCB :
        proofSearch k (.plays (.bot CooperateBot)
          (.search k (.plays .opp .self .C) (.const .C) (.const .D)) .C) = true
    · unfold OBot DupocBot at hn
      simp [play, eval, Prog.subst, Formula.subst, hCB, hDFalse] at hn
    · have hCBFalse :
          proofSearch k (.plays (.bot CooperateBot)
            (.search k (.plays .opp .self .C) (.const .C) (.const .D)) .C) = false := by
        cases h : proofSearch k _ with
        | true => exact absurd h hCB
        | false => rfl
      unfold OBot DupocBot at hn
      simp [play, eval, Prog.subst, Formula.subst, hCBFalse, hDFalse, hDC] at hn
  | succ m =>
  cases m with
  | zero =>
    by_cases hCB :
        proofSearch k (.plays (.bot CooperateBot)
          (.search k (.plays .opp .self .C) (.const .C) (.const .D)) .C) = true
    · unfold OBot DupocBot at hn
      simp [play, eval, Prog.subst, Formula.subst, hCB, hDFalse, hDC] at hn
    · have hCBFalse :
          proofSearch k (.plays (.bot CooperateBot)
            (.search k (.plays .opp .self .C) (.const .C) (.const .D)) .C) = false := by
        cases h : proofSearch k _ with
        | true => exact absurd h hCB
        | false => rfl
      unfold OBot DupocBot at hn
      simp [play, eval, Prog.subst, Formula.subst, hCBFalse, hDFalse, hDC] at hn
  | succ fuel =>
    have hD : play (fuel + 6) OBot (DupocBot k) = some .D :=
      OBot_plays_D_against_DupocBot k fuel
    have heq : fuel + 1 + 1 + 1 + 1 + 1 + 1 = fuel + 6 := by omega
    rw [heq, hD] at hn
    cases hn

theorem proofSearch_false_OBot_C_dupoc (k : Nat) :
    proofSearch k (.plays OBot (DupocBot k) .C) = false := by
  cases h : proofSearch k (.plays OBot (DupocBot k) .C) with
  | true => exact absurd (proofSearch_sound _ _ h) (interp_OBot_plays_C_false_dupoc k)
  | false => rfl

theorem DupocBot_plays_D_against_OBot (k fuel : Nat) :
    play (fuel + 2) (DupocBot k) OBot = some .D := by
  have hg := proofSearch_false_OBot_C_dupoc k
  show eval (fuel + 2) (DupocBot k) OBot (DupocBot k) = some .D
  unfold DupocBot at hg ⊢
  simp [eval, Prog.subst, Formula.subst, hg]

theorem llm_outcome_DupocBot_vs_OBot (k n : Nat) :
    outcome (n + 6) (DupocBot k) OBot = some (.D, .D) := by
  have hA : play (n + 6) (DupocBot k) OBot = some .D := by
    have h : play ((n + 4) + 2) (DupocBot k) OBot = some .D :=
      DupocBot_plays_D_against_OBot k (n + 4)
    have heq : n + 4 + 2 = n + 6 := by omega
    rw [heq] at h
    exact h
  have hB : play (n + 6) OBot (DupocBot k) = some .D :=
    OBot_plays_D_against_DupocBot k n
  exact outcome_of_plays _ _ _ _ _ hA hB

end PD.Theorems
