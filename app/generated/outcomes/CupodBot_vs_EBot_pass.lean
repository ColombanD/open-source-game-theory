import PrisonersDilemma.Bots.CupodBot
import PrisonersDilemma.Bots.EBot
import PrisonersDilemma.Bots.CooperateBot
import PrisonersDilemma.Bots.DefectBot
import PrisonersDilemma.Bots.MirrorBot
import PrisonersDilemma.Theorems.CooperateBot
import PrisonersDilemma.Theorems.DefectBot
import PrisonersDilemma.Theorems.Helpers
import PrisonersDilemma.Theorems.ProofSearch
import PrisonersDilemma.Axioms

open PD
open PD.Axioms
open PD.Bots

namespace PD.Theorems

private theorem cupod_mono (n k : Nat) (Bot : Prog) (a : Action) :
    n ≤ k →
    proofSearch k (.plays Bot (CupodBot n) a) = true →
    proofSearch k (.plays Bot (CupodBot k) a) = true := by
  intro hle hnk
  let Φ : Nat → Formula := fun i => Formula.plays Bot (CupodBot i) a
  obtain ⟨w, hw, hwk⟩ := (proofSearch_spec k (Φ n)).1 hnk
  obtain ⟨w', hw', hwk'⟩ := witness_transport_family Φ n k hle w hw hwk
  exact (proofSearch_spec k (Φ k)).2 ⟨w', hw', hwk'⟩

private theorem ps_true_botDB_CupodBot :
    ∃ k, proofSearch k (.plays (.bot DefectBot) (CupodBot k) .D) = true := by
  have hex : ∃ m, play m (.bot DefectBot) (CupodBot 0) = some .D := by
    refine ⟨2, ?_⟩
    rfl
  obtain ⟨K, hK⟩ :=
    proofSearch_complete_plays (.bot DefectBot) (CupodBot 0) .D hex
  exact ⟨K, cupod_mono 0 K (.bot DefectBot) .D (Nat.zero_le K) hK⟩

private theorem cupod_plays_D_vs_botDB (k fuel : Nat)
    (hk : proofSearch k (.plays (.bot DefectBot) (CupodBot k) .D) = true) :
    play (fuel + 2) (CupodBot k) (.bot DefectBot) = some .D := by
  show eval (fuel + 2) (CupodBot k) (.bot DefectBot) (CupodBot k) = some .D
  unfold CupodBot at hk ⊢
  simp [eval, Prog.subst, Formula.subst, hk]

private theorem cupod_plays_C_vs_botCB (k fuel : Nat) :
    play (fuel + 2) (CupodBot k) (.bot CooperateBot) = some .C := by
  have hf : proofSearch k (.plays (.bot CooperateBot) (CupodBot k) .D) = false := by
    cases h : proofSearch k (.plays (.bot CooperateBot) (CupodBot k) .D) with
    | true => exact absurd (proofSearch_sound _ _ h) (interp_bot_CooperateBot_plays_D_false _)
    | false => rfl
  show eval (fuel + 2) (CupodBot k) (.bot CooperateBot) (CupodBot k) = some .C
  unfold CupodBot at hf ⊢
  simp [eval, Prog.subst, Formula.subst, hf]

private theorem EBot_plays_C_vs_CupodBot (k fuel : Nat)
    (hk : proofSearch k (.plays (.bot DefectBot) (CupodBot k) .D) = true) :
    play (fuel + 5) EBot (CupodBot k) = some .C := by
  have h1 : play (fuel + 3) (CupodBot k) (.bot DefectBot) = some .D := by
    simpa [Nat.add_assoc] using cupod_plays_D_vs_botDB k (fuel + 1) hk
  have hG1 :
      eval (fuel + 4) EBot (CupodBot k) (.sim .opp (.bot DefectBot)) = some .D := by
    simpa [Nat.add_assoc] using
      eval_sim_opp_bot_of_play (fuel + 3) EBot (CupodBot k) DefectBot .D h1
  have h2 : play (fuel + 2) (CupodBot k) (.bot CooperateBot) = some .C :=
    cupod_plays_C_vs_botCB k fuel
  have hG2 :
      eval (fuel + 3) EBot (CupodBot k) (.sim .opp (.bot CooperateBot)) = some .C := by
    simpa [Nat.add_assoc] using
      eval_sim_opp_bot_of_play (fuel + 2) EBot (CupodBot k) CooperateBot .C h2
  have hInner :
      eval (fuel + 4) EBot (CupodBot k)
        (.ite (.sim .opp (.bot CooperateBot)) Action.C (.const Action.C)
          (.ite (.sim .opp (.bot MirrorBot)) Action.C (.const Action.C) (.const Action.D))) =
        some .C := by
    simpa [Nat.add_assoc] using
      eval_ite_from_guard (fuel + 3) EBot (CupodBot k)
        (.sim .opp (.bot CooperateBot)) (.const Action.C)
        (.ite (.sim .opp (.bot MirrorBot)) Action.C (.const Action.C) (.const Action.D))
        Action.C Action.C hG2
  have hPlay := play_ite_from_guard
    fuel 4 EBot (CupodBot k) (.sim .opp (.bot DefectBot))
    (.const Action.D)
    (.ite (.sim .opp (.bot CooperateBot)) Action.C (.const Action.C)
      (.ite (.sim .opp (.bot MirrorBot)) Action.C (.const Action.C) (.const Action.D)))
    Action.C Action.D
    (by rfl) hG1
  simpa [Nat.add_assoc, hInner] using hPlay

private theorem interp_EBot_plays_D_vs_CupodBot_false (k : Nat)
    (hk : proofSearch k (.plays (.bot DefectBot) (CupodBot k) .D) = true) :
    ¬ (Formula.plays EBot (CupodBot k) .D).interp := by
  rintro ⟨n, hn⟩
  cases n with
  | zero => simp [play, eval] at hn
  | succ n => cases n with
    | zero => simp [play, eval, EBot] at hn
    | succ n => cases n with
      | zero => simp [play, eval, EBot] at hn
      | succ n => cases n with
        | zero => simp [play, eval, EBot, Prog.subst, CupodBot] at hn
        | succ n => cases n with
          | zero =>
              simp only [CupodBot] at hk
              simp [play, eval, EBot, Prog.subst, CupodBot, Formula.subst, hk] at hn
              exact absurd hn (by decide)
          | succ fuel =>
              have hC : play (fuel + 5) EBot (CupodBot k) = some .C :=
                EBot_plays_C_vs_CupodBot k fuel hk
              have hn' : play (fuel + 5) EBot (CupodBot k) = some .D := hn
              rw [hC] at hn'
              cases hn'

private theorem ps_false_EBot_CupodBot (k : Nat)
    (hk : proofSearch k (.plays (.bot DefectBot) (CupodBot k) .D) = true) :
    proofSearch k (.plays EBot (CupodBot k) .D) = false := by
  cases h : proofSearch k (.plays EBot (CupodBot k) .D) with
  | true =>
    exact absurd (proofSearch_sound _ _ h)
      (interp_EBot_plays_D_vs_CupodBot_false k hk)
  | false => rfl

theorem llm_outcome_CupodBot_vs_EBot (n : Nat) :
    ∃ k, outcome (n + 5) (CupodBot k) EBot = some (.C, .C) := by
  obtain ⟨k, hk⟩ := ps_true_botDB_CupodBot
  refine ⟨k, ?_⟩
  have hF : proofSearch k (.plays EBot (CupodBot k) .D) = false :=
    ps_false_EBot_CupodBot k hk
  have hA : play (n + 5) (CupodBot k) EBot = some .C := by
    show eval (n + 5) (CupodBot k) EBot (CupodBot k) = some .C
    unfold CupodBot at hF ⊢
    simp [eval, Prog.subst, Formula.subst, hF]
  have hB : play (n + 5) EBot (CupodBot k) = some .C :=
    EBot_plays_C_vs_CupodBot k n hk
  exact outcome_of_plays _ _ _ _ _ hA hB

end PD.Theorems
