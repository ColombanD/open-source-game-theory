import PrisonersDilemma.Bots.LlmGenerations.GuardianBot
import PrisonersDilemma.Bots.OBot
import PrisonersDilemma.Bots.CooperateBot
import PrisonersDilemma.Bots.DefectBot
import PrisonersDilemma.Dynamics
import PrisonersDilemma.Base.Helpers
import PrisonersDilemma.BaseTheorems
import PrisonersDilemma.Theorems.CooperateBot.Helpers

open PD PD.Bots PD.BaseTheorems
namespace PD.Theorems

-- === GuardianBot cooperates with OBot ===

theorem guardian_obot_probe_botCB (fuel : Nat) :
    play (fuel + 6) OBot (.bot CooperateBot) = some .C := by
  apply play_from_eval
  unfold OBot CooperateBot
  simp [eval, Prog.subst]
  decide

theorem guardian_obot_interp_botCB_D_false :
    ¬ (Formula.plays OBot (.bot CooperateBot) .D).interp := by
  rintro ⟨n, hn⟩
  have hC : play (n + 6) OBot (.bot CooperateBot) = some .C := guardian_obot_probe_botCB n
  have hD : play (n + 6) OBot (.bot CooperateBot) = some .D := by
    unfold play at hn ⊢
    exact eval_mono_le hn (n+6) (by omega)
  rw [hC] at hD; cases hD

theorem guardian_obot_proofSearch_false (k : Nat) :
    proofSearch k (.plays OBot (.bot CooperateBot) .D) = false := by
  cases h : proofSearch k (.plays OBot (.bot CooperateBot) .D) with
  | true  => exact absurd (proofSearch_sound _ _ h) guardian_obot_interp_botCB_D_false
  | false => rfl

theorem guardian_plays_C_vs_OBot (k fuel : Nat) :
    play (fuel + 2) (GuardianBot k) OBot = some .C := by
  have hg := guardian_obot_proofSearch_false k
  show eval (fuel + 2) (GuardianBot k) OBot (GuardianBot k) = some .C
  unfold GuardianBot
  simp [eval, Prog.subst, Formula.subst, hg]

-- === OBot defects against GuardianBot ===

theorem guardian_plays_C_vs_botCB (k fuel : Nat) :
    play (fuel + 2) (GuardianBot k) (.bot CooperateBot) = some .C := by
  have hg : proofSearch k (.plays (.bot CooperateBot) (.bot CooperateBot) .D) = false := by
    cases h : proofSearch k (.plays (.bot CooperateBot) (.bot CooperateBot) .D) with
    | true  => exact absurd (proofSearch_sound _ _ h)
                            (interp_bot_CooperateBot_plays_D_false _)
    | false => rfl
  show eval (fuel + 2) (GuardianBot k) (.bot CooperateBot) (GuardianBot k) = some .C
  unfold GuardianBot
  simp [eval, Prog.subst, Formula.subst, hg]

theorem guardian_plays_D_vs_botDB (k fuel : Nat) :
    play (fuel + 2) (GuardianBot (k+2)) (.bot DefectBot) = some .D := by
  have hg : proofSearch (k+2) (.plays (.bot DefectBot) (.bot CooperateBot) .D) = true :=
    (proofSearch_spec _ _).2 (Pf.atom ⟨PlaysProof.bot PlaysProof.const, by simp only [c_leaf, c_node]; omega⟩)
  show eval (fuel + 2) (GuardianBot (k+2)) (.bot DefectBot) (GuardianBot (k+2)) = some .D
  unfold GuardianBot
  simp [eval, Prog.subst, Formula.subst, hg]

theorem obot_plays_D_vs_guardian (k fuel : Nat) :
    play (fuel + 5) OBot (GuardianBot (k+2)) = some .D := by
  have hGuard1 : eval (fuel + 4) OBot (GuardianBot (k+2)) (.sim .opp (.bot CooperateBot)) = some .C := by
    have hProbe : play (fuel + 3) (GuardianBot (k+2)) (.bot CooperateBot) = some .C := by
      simpa [Nat.add_assoc] using guardian_plays_C_vs_botCB (k+2) (fuel + 1)
    simpa [Nat.add_assoc] using
      (eval_sim_opp_bot_of_play (fuel + 3) OBot (GuardianBot (k+2)) CooperateBot Action.C hProbe)
  have hGuard2 : eval (fuel + 3) OBot (GuardianBot (k+2)) (.sim .opp (.bot DefectBot)) = some .D := by
    have hProbe : play (fuel + 2) (GuardianBot (k+2)) (.bot DefectBot) = some .D :=
      guardian_plays_D_vs_botDB k fuel
    simpa [Nat.add_assoc] using
      (eval_sim_opp_bot_of_play (fuel + 2) OBot (GuardianBot (k+2)) DefectBot Action.D hProbe)
  have hPlay := play_ite_from_guard
    fuel 4 OBot (GuardianBot (k+2)) (.sim .opp (.bot CooperateBot))
    (.ite (.sim .opp (.bot DefectBot)) Action.C (.const Action.C) (.const Action.D))
    (.const Action.D)
    Action.C Action.C
    (by rfl) hGuard1
  have hInner : eval (fuel + 4) OBot (GuardianBot (k+2))
      (.ite (.sim .opp (.bot DefectBot)) Action.C (.const Action.C) (.const Action.D)) = some .D := by
    simpa [Nat.add_assoc] using
      (eval_ite_from_guard (fuel + 3) OBot (GuardianBot (k+2))
        (.sim .opp (.bot DefectBot)) (.const Action.C) (.const Action.D)
        Action.C Action.D hGuard2)
  simpa [hInner] using hPlay

-- === Final outcome theorem ===

theorem llm_outcome_GuardianBot_vs_OBot :
    ∃ k₂, ∀ k, k₂ < k →
      ∃ fuel, outcome fuel (GuardianBot k) OBot = some (.C, .D) := by
  refine ⟨1, fun k hk => ?_⟩
  obtain ⟨j, rfl⟩ : ∃ j, k = j + 2 := ⟨k - 2, by omega⟩
  refine ⟨7, ?_⟩
  have hA : play 7 (GuardianBot (j+2)) OBot = some .C := by
    simpa using guardian_plays_C_vs_OBot (j+2) 5
  have hB : play 7 OBot (GuardianBot (j+2)) = some .D := by
    simpa using obot_plays_D_vs_guardian j 2
  exact outcome_of_plays _ _ _ _ _ hA hB

end PD.Theorems

