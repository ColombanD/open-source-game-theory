import PrisonersDilemma.Bots.CupodBot
import PrisonersDilemma.Bots.DBot
import PrisonersDilemma.Bots.DefectBot
import PrisonersDilemma.Axioms
import PrisonersDilemma.Theorems.Helpers
import PrisonersDilemma.Theorems.ProofSearch
import PrisonersDilemma.Theorems.DefectBot

open PDNew
open PDNew.Axioms
open PDNew.Bots
namespace PDNew.Theorems

private theorem cupod_search_succeeds_aux :
    ∃ k, proofSearch k (.plays (.bot DefectBot) (CupodBot k) .D) = true := by
  have h : ∃ n, play n (.bot DefectBot) (CupodBot 0) = some .D := by
    refine ⟨2, ?_⟩
    show eval 2 (.bot DefectBot) (CupodBot 0) (.bot DefectBot) = some .D
    simp [eval, DefectBot]
  obtain ⟨k', hk'⟩ := proofSearch_complete_plays _ _ _ h
  let Φ : Nat → Formula := fun i => .plays (.bot DefectBot) (CupodBot i) .D
  obtain ⟨w, hw, hwk⟩ := (proofSearch_spec k' (Φ 0)).1 hk'
  obtain ⟨w', hw', hwk'⟩ := witness_transport_family Φ 0 k' (Nat.zero_le _) w hw hwk
  exact ⟨k', (proofSearch_spec k' (Φ k')).2 ⟨w', hw', hwk'⟩⟩

private theorem DBot_plays_C_against_CupodBot_aux (k fuel : Nat)
    (hk : proofSearch k (.plays (.bot DefectBot) (CupodBot k) .D) = true) :
    play (fuel + 4) DBot (CupodBot k) = some .C := by
  have hCupodVsD : play (fuel + 2) (CupodBot k) (.bot DefectBot) = some .D := by
    show eval (fuel + 2) (CupodBot k) (.bot DefectBot) (CupodBot k) = some .D
    unfold CupodBot at hk ⊢
    simp [eval, Prog.subst, Formula.subst, hk]
  have hGuard : eval (fuel + 3) DBot (CupodBot k) (.sim .opp (.bot DefectBot)) = some .D :=
    eval_sim_opp_bot_of_play _ _ _ _ _ hCupodVsD
  have hPlay := play_ite_from_guard
    fuel 3 DBot (CupodBot k) (.sim .opp (.bot DefectBot))
    (.const .D) (.const .C) .C .D (by rfl) hGuard
  simpa [eval] using hPlay

private theorem CupodBot_plays_C_against_DBot_aux (k fuel : Nat)
    (hfalse : proofSearch k (.plays DBot (CupodBot k) .D) = false) :
    play (fuel + 2) (CupodBot k) DBot = some .C := by
  show eval (fuel + 2) (CupodBot k) DBot (CupodBot k) = some .C
  unfold CupodBot at hfalse ⊢
  simp [eval, Prog.subst, Formula.subst, hfalse]

private theorem play_DBot_vs_CupodBot_small (k : Nat) :
    play 0 DBot (CupodBot k) = none ∧
    play 1 DBot (CupodBot k) = none ∧
    play 2 DBot (CupodBot k) = none ∧
    play 3 DBot (CupodBot k) = none := by
  refine ⟨rfl, ?_, ?_, ?_⟩
  · show eval 1 DBot (CupodBot k) DBot = none
    simp [eval, DBot]
  · show eval 2 DBot (CupodBot k) DBot = none
    simp [eval, DBot]
  · show eval 3 DBot (CupodBot k) DBot = none
    unfold DBot CupodBot
    simp [eval, Prog.subst, Formula.subst]

private theorem DBot_never_plays_D_vs_CupodBot_aux (k : Nat)
    (hk : proofSearch k (.plays (.bot DefectBot) (CupodBot k) .D) = true) :
    ¬ ∃ n, play n DBot (CupodBot k) = some .D := by
  rintro ⟨n, hn⟩
  obtain ⟨h0, h1, h2, h3⟩ := play_DBot_vs_CupodBot_small k
  match n, hn with
  | 0, hn => rw [h0] at hn; cases hn
  | 1, hn => rw [h1] at hn; cases hn
  | 2, hn => rw [h2] at hn; cases hn
  | 3, hn => rw [h3] at hn; cases hn
  | n+4, hn =>
    have h := DBot_plays_C_against_CupodBot_aux k n hk
    rw [h] at hn; cases hn

private theorem cupod_DBot_search_fails_aux (k : Nat)
    (hk : proofSearch k (.plays (.bot DefectBot) (CupodBot k) .D) = true) :
    proofSearch k (.plays DBot (CupodBot k) .D) = false := by
  cases h : proofSearch k (.plays DBot (CupodBot k) .D) with
  | false => rfl
  | true =>
    exfalso
    have hi := proofSearch_sound k _ h
    exact DBot_never_plays_D_vs_CupodBot_aux k hk hi

theorem llm_outcome_CupodBot_vs_DBot :
    ∃ k, ∀ n, outcome (n + 4) (CupodBot k) DBot = some (.C, .C) := by
  obtain ⟨k, hk⟩ := cupod_search_succeeds_aux
  refine ⟨k, fun n => ?_⟩
  have hFalse := cupod_DBot_search_fails_aux k hk
  have hA : play (n + 4) (CupodBot k) DBot = some .C := by
    have := CupodBot_plays_C_against_DBot_aux k (n + 2) hFalse
    simpa [Nat.add_assoc] using this
  have hB : play (n + 4) DBot (CupodBot k) = some .C :=
    DBot_plays_C_against_CupodBot_aux k n hk
  exact outcome_of_plays _ _ _ _ _ hA hB

end PDNew.Theorems
