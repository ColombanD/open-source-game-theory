import PrisonersDilemma.Program
import PrisonersDilemma.Dynamics
import PrisonersDilemma.Axioms
import PrisonersDilemma.Bots.DupocBot
import PrisonersDilemma.Bots.EBot
import PrisonersDilemma.Bots.DefectBot
import PrisonersDilemma.Bots.CooperateBot
import PrisonersDilemma.Bots.MirrorBot
import PrisonersDilemma.Theorems.DefectBot
import PrisonersDilemma.Theorems.CooperateBot
import PrisonersDilemma.Theorems.Helpers
import PrisonersDilemma.Theorems.ProofSearch

open PD
open PD.Axioms
open PD.Bots

namespace PD.Theorems

-- play (n+2) (.bot DefectBot) q = some .D
theorem play_bot_DefectBot_lemma (n : Nat) (q : Prog) :
    play (n+2) (.bot DefectBot) q = some .D := by
  simp [play, eval, DefectBot]

-- interp ".bot DefectBot plays C" is false
theorem interp_bot_DefectBot_plays_C_false (q : Prog) :
    ¬ (Formula.plays (.bot DefectBot) q .C).interp := by
  rintro ⟨n, hn⟩
  cases n with
  | zero => simp [play, eval] at hn
  | succ m =>
      cases m with
      | zero => simp [play, eval] at hn
      | succ fuel =>
          rw [play_bot_DefectBot_lemma fuel q] at hn
          cases hn

-- proofSearch k ".plays (.bot DefectBot) (DupocBot k) C" is false
theorem proofSearch_false_bot_DefectBot (k : Nat) :
    proofSearch k (.plays (.bot DefectBot) (DupocBot k) .C) = false := by
  cases h : proofSearch k (.plays (.bot DefectBot) (DupocBot k) .C) with
  | true => exact absurd (proofSearch_sound _ _ h) (interp_bot_DefectBot_plays_C_false _)
  | false => rfl

-- DupocBot plays D against .bot DefectBot
theorem DupocBot_plays_D_against_bot_DefectBot (k fuel : Nat) :
    play (fuel + 2) (DupocBot k) (.bot DefectBot) = some .D := by
  have hg := proofSearch_false_bot_DefectBot k
  show eval (fuel + 2) (DupocBot k) (.bot DefectBot) (DupocBot k) = some .D
  unfold DupocBot at hg ⊢
  simp [eval, Prog.subst, Formula.subst, hg]

-- DupocBot plays C against .bot CooperateBot given proofSearch succeeds
theorem DupocBot_plays_C_against_bot_CooperateBot_lemma (k fuel : Nat)
    (hk : proofSearch k (.plays (.bot CooperateBot) (DupocBot k) .C) = true) :
    play (fuel + 2) (DupocBot k) (.bot CooperateBot) = some .C := by
  show eval (fuel + 2) (DupocBot k) (.bot CooperateBot) (DupocBot k) = some .C
  unfold DupocBot at hk ⊢
  simp [eval, Prog.subst, Formula.subst, hk]

-- Get k such that proofSearch k for .plays (.bot CooperateBot) (DupocBot k) C succeeds
theorem proofSearch_true_bot_CooperateBot_DupocBot :
    ∃ k, proofSearch k (.plays (.bot CooperateBot) (DupocBot k) .C) = true := by
  have hex : ∃ m, play m (.bot CooperateBot) (DupocBot 0) = some .C :=
    ⟨2, play_bot_CooperateBot 0 (DupocBot 0)⟩
  obtain ⟨w, hw⟩ := witness_complete_plays _ _ _ hex
  let Φ : Nat → Formula := fun k => .plays (.bot CooperateBot) (DupocBot k) .C
  let k := witnessChars w
  obtain ⟨w', hw', hwk'⟩ := witness_transport_family Φ 0 k (Nat.zero_le k) w hw (Nat.le_refl k)
  exact ⟨k, (proofSearch_spec k (Φ k)).2 ⟨w', hw', hwk'⟩⟩

-- EBot plays C against DupocBot k given the relevant proofSearch
theorem EBot_plays_C_against_DupocBot_lemma (k fuel : Nat)
    (hk : proofSearch k (.plays (.bot CooperateBot) (DupocBot k) .C) = true) :
    play (fuel + 5) EBot (DupocBot k) = some .C := by
  have hDup_D : play (fuel + 3) (DupocBot k) (.bot DefectBot) = some .D := by
    simpa [Nat.add_assoc] using DupocBot_plays_D_against_bot_DefectBot k (fuel + 1)
  have hGuard1 :
      eval (fuel + 4) EBot (DupocBot k) (.sim .opp (.bot DefectBot)) = some .D := by
    simpa [Nat.add_assoc] using
      (eval_sim_opp_bot_of_play (fuel + 3) EBot (DupocBot k) DefectBot Action.D hDup_D)
  have hDup_C : play (fuel + 2) (DupocBot k) (.bot CooperateBot) = some .C :=
    DupocBot_plays_C_against_bot_CooperateBot_lemma k fuel hk
  have hGuard2 :
      eval (fuel + 3) EBot (DupocBot k) (.sim .opp (.bot CooperateBot)) = some .C := by
    simpa [Nat.add_assoc] using
      (eval_sim_opp_bot_of_play (fuel + 2) EBot (DupocBot k) CooperateBot Action.C hDup_C)
  have hInner :
      eval (fuel + 4) EBot (DupocBot k)
        (.ite (.sim .opp (.bot CooperateBot)) Action.C (.const Action.C)
          (.ite (.sim .opp (.bot MirrorBot)) Action.C (.const Action.C) (.const Action.D))) =
        some .C := by
    simpa [Nat.add_assoc] using
      (eval_ite_from_guard (fuel + 3) EBot (DupocBot k)
        (.sim .opp (.bot CooperateBot)) (.const Action.C)
        (.ite (.sim .opp (.bot MirrorBot)) Action.C (.const Action.C) (.const Action.D))
        Action.C Action.C hGuard2)
  have hPlay := play_ite_from_guard
    fuel 4 EBot (DupocBot k) (.sim .opp (.bot DefectBot))
    (.const Action.D)
    (.ite (.sim .opp (.bot CooperateBot)) Action.C (.const Action.C)
      (.ite (.sim .opp (.bot MirrorBot)) Action.C (.const Action.C) (.const Action.D)))
    Action.C Action.D
    (by rfl) hGuard1
  simpa [Nat.add_assoc, hInner] using hPlay

theorem llm_outcome_DupocBot_vs_EBot (n : Nat) :
    ∃ k, outcome (n+5) (DupocBot k) EBot = some (.C, .C) := by
  obtain ⟨k_C, hk_C⟩ := proofSearch_true_bot_CooperateBot_DupocBot
  have hex_E : ∃ m, play m EBot (DupocBot k_C) = some .C :=
    ⟨5, EBot_plays_C_against_DupocBot_lemma k_C 0 hk_C⟩
  obtain ⟨w_E, hw_E⟩ := witness_complete_plays EBot (DupocBot k_C) .C hex_E
  let k := max k_C (witnessChars w_E)
  have hk_ge_kC : k_C ≤ k := Nat.le_max_left _ _
  have hk_ge_wE : witnessChars w_E ≤ k := Nat.le_max_right _ _
  have hPS_coop : proofSearch k (.plays (.bot CooperateBot) (DupocBot k) .C) = true := by
    let Φ : Nat → Formula := fun i => .plays (.bot CooperateBot) (DupocBot i) .C
    obtain ⟨w0, hw0, hw0k⟩ := (proofSearch_spec k_C (Φ k_C)).1 hk_C
    have hw0_kfinal : witnessChars w0 ≤ k := Nat.le_trans hw0k hk_ge_kC
    obtain ⟨w', hw', hwk'⟩ := witness_transport_family Φ k_C k hk_ge_kC w0 hw0 hw0_kfinal
    exact (proofSearch_spec k (Φ k)).2 ⟨w', hw', hwk'⟩
  have hPS_E : proofSearch k (.plays EBot (DupocBot k) .C) = true := by
    let Ψ : Nat → Formula := fun i => .plays EBot (DupocBot i) .C
    obtain ⟨w', hw', hwk'⟩ := witness_transport_family Ψ k_C k hk_ge_kC w_E hw_E hk_ge_wE
    exact (proofSearch_spec k (Ψ k)).2 ⟨w', hw', hwk'⟩
  refine ⟨k, ?_⟩
  have hA : play (n+5) (DupocBot k) EBot = some .C := by
    show eval (n+5) (DupocBot k) EBot (DupocBot k) = some .C
    unfold DupocBot at hPS_E ⊢
    simp [eval, Prog.subst, Formula.subst, hPS_E]
  have hB : play (n+5) EBot (DupocBot k) = some .C :=
    EBot_plays_C_against_DupocBot_lemma k n hPS_coop
  exact outcome_of_plays _ _ _ _ _ hA hB

end PD.Theorems
