import PrisonersDilemma.Bots.LlmGenerations.DIMCID
import PrisonersDilemma.Bots.TitForTatBot
import PrisonersDilemma.Bots.CooperateBot
import PrisonersDilemma.Dynamics
import PrisonersDilemma.Base.Helpers
import PrisonersDilemma.BaseTheorems
import PrisonersDilemma.Theorems.CooperateBot.Helpers

open PD
open PD.BaseTheorems
open PD.Bots
namespace PD.Theorems

/-- The DIMCID guard against `.bot CooperateBot`. -/
abbrev dimcidTFT_guard_botCoop (k : Nat) : Formula :=
  .impl (.plays (DIMCID k) (.bot CooperateBot) Action.C)
        (.plays (.bot CooperateBot) (DIMCID k) Action.D)

/-- The consequent `.bot CooperateBot plays D vs DIMCID` is unprovable. -/
theorem dimcidTFT_consequent_botCoop_not_provable (k m : Nat) :
    ¬ Pf m (.plays (.bot CooperateBot) (DIMCID k) Action.D) := by
  intro h
  exact interp_bot_CooperateBot_plays_D_false (DIMCID k) (Pf_sound m _ h)

theorem dimcidTFT_no_provable_botCoop (k : Nat) :
    ∀ {m : Nat} {φ : Formula}, Pf m φ →
      ¬ TailTo (.plays (.bot CooperateBot) (DIMCID k) Action.D) φ :=
  no_provable_tailTo_unreadable _ _ _
    (fun n hA => dimcidTFT_consequent_botCoop_not_provable k n (.atom hA))
    (by rintro (⟨_, _, _, _, h⟩ | ⟨_, _, h⟩ | ⟨_, _, h⟩ | ⟨_, _, _, _, h⟩ |
          ⟨_, _, _, _, _, _, _, h⟩ | ⟨_, _, _, _, _, _, _, h⟩) <;> simp [CooperateBot] at h)
    (by intro L h
        cases L with
        | nil => simp [searchPlug, CooperateBot] at h
        | cons hd tl => obtain ⟨g, ψ, e⟩ := hd; simp [searchPlug, CooperateBot] at h)
    (by intro hd L h
        cases hd with
        | searchL g' ψ' e' => simp [ctxPlug, CooperateBot] at h
        | iteL z' aT' other' => simp [ctxPlug, CooperateBot] at h)

theorem dimcidTFT_guard_botCoop_not_provable (k : Nat) :
    ¬ Pf k (dimcidTFT_guard_botCoop k) := by
  intro h
  refine dimcidTFT_no_provable_botCoop k h ?_
  exact ⟨rfl, by simp [DIMCID, CooperateBot]⟩

theorem dimcidTFT_proofSearch_false_botCoop (k : Nat) :
    proofSearch k
      ((Formula.impl (.plays .self .opp Action.C) (.plays .opp .self Action.D)).subst
        (DIMCID k) (.bot CooperateBot)) = false := by
  show proofSearch k (dimcidTFT_guard_botCoop k) = false
  cases hps : proofSearch k (dimcidTFT_guard_botCoop k) with
  | false => rfl
  | true => exact absurd ((proofSearch_spec k _).1 hps) (dimcidTFT_guard_botCoop_not_provable k)

/-- DIMCID cooperates against `.bot CooperateBot`: its guard fails. -/
theorem DIMCID_plays_C_against_botCoop (k fuel : Nat) :
    play (fuel + 2) (DIMCID k) (.bot CooperateBot) = some .C := by
  show (if proofSearch k
            ((Formula.impl (.plays .self .opp Action.C) (.plays .opp .self Action.D)).subst
              (DIMCID k) (.bot CooperateBot))
          then eval (fuel + 1) (DIMCID k) (.bot CooperateBot) (.const Action.D)
          else eval (fuel + 1) (DIMCID k) (.bot CooperateBot) (.const Action.C)) = some .C
  rw [dimcidTFT_proofSearch_false_botCoop k]; simp [eval]

/-- TFT cooperates with DIMCID: its probe sees DIMCID cooperate vs `.bot CooperateBot`. -/
theorem TitForTatBot_plays_C_against_DIMCID (k fuel : Nat) :
    play (fuel + 4) TitForTatBot (DIMCID k) = some .C := by
  have hDimcid : play (fuel + 2) (DIMCID k) (.bot CooperateBot) = some .C :=
    DIMCID_plays_C_against_botCoop k fuel
  have hGuard :
      eval (fuel + 3) TitForTatBot (DIMCID k) (.sim .opp (.bot CooperateBot)) = some .C := by
    simpa [Nat.add_assoc] using
      (eval_sim_opp_bot_of_play (fuel + 2) TitForTatBot (DIMCID k) CooperateBot Action.C hDimcid)
  have hPlay := play_ite_from_guard
    fuel 3 TitForTatBot (DIMCID k) (.sim .opp (.bot CooperateBot))
    (.const Action.C) (.const Action.D)
    Action.C Action.C
    (by rfl) hGuard
  simpa [eval] using hPlay

/-- TFT never plays D against DIMCID. -/
theorem interp_TitForTatBot_D_vs_DIMCID_false (k : Nat) :
    ¬ (Formula.plays TitForTatBot (DIMCID k) Action.D).interp := by
  rintro ⟨n, hn⟩
  have hC : play (n + 4) TitForTatBot (DIMCID k) = some .C :=
    TitForTatBot_plays_C_against_DIMCID k n
  have hD : play (n + 4) TitForTatBot (DIMCID k) = some .D := by
    unfold play at hn ⊢; exact eval_mono_le hn (n + 4) (by omega)
  rw [hC] at hD; cases hD

/-- The consequent `TFT plays D vs DIMCID` is unprovable (it's false). -/
theorem dimcidTFT_consequent_TFT_not_provable (k m : Nat) :
    ¬ Pf m (.plays TitForTatBot (DIMCID k) Action.D) := by
  intro h
  exact interp_TitForTatBot_D_vs_DIMCID_false k (Pf_sound m _ h)

theorem dimcidTFT_no_provable_TFT (k : Nat) :
    ∀ {m : Nat} {φ : Formula}, Pf m φ →
      ¬ TailTo (.plays TitForTatBot (DIMCID k) Action.D) φ :=
  no_provable_tailTo_unreadable _ _ _
    (fun n hA => dimcidTFT_consequent_TFT_not_provable k n (.atom hA))
    (by rintro (⟨_, _, _, _, h⟩ | ⟨_, _, h⟩ | ⟨_, _, h⟩ | ⟨_, _, _, _, h⟩ |
          ⟨_, _, _, _, _, _, _, h⟩ | ⟨_, _, _, _, _, _, _, h⟩) <;> simp [TitForTatBot] at h)
    (by intro L h
        cases L with
        | nil => simp [searchPlug, TitForTatBot] at h
        | cons hd tl => obtain ⟨g, ψ, e⟩ := hd; simp [searchPlug, TitForTatBot] at h)
    (by intro hd L h
        cases hd with
        | searchL g' ψ' e' => simp [ctxPlug, TitForTatBot] at h
        | iteL z' aT' other' =>
            simp only [TitForTatBot, ctxPlug, Prog.ite.injEq] at h
            exact const_ne_ctxPlug (by decide) L h.2.2.1)

/-- The DIMCID guard against TFT. -/
abbrev dimcidTFT_guard (k : Nat) : Formula :=
  .impl (.plays (DIMCID k) TitForTatBot Action.C)
        (.plays TitForTatBot (DIMCID k) Action.D)

theorem dimcidTFT_guard_not_provable (k : Nat) :
    ¬ Pf k (dimcidTFT_guard k) := by
  intro h
  refine dimcidTFT_no_provable_TFT k h ?_
  exact ⟨rfl, by simp [DIMCID, TitForTatBot]⟩

theorem dimcidTFT_proofSearch_false (k : Nat) :
    proofSearch k
      ((Formula.impl (.plays .self .opp Action.C) (.plays .opp .self Action.D)).subst
        (DIMCID k) TitForTatBot) = false := by
  show proofSearch k (dimcidTFT_guard k) = false
  cases hps : proofSearch k (dimcidTFT_guard k) with
  | false => rfl
  | true => exact absurd ((proofSearch_spec k _).1 hps) (dimcidTFT_guard_not_provable k)

theorem DIMCID_plays_C_against_TitForTatBot (k fuel : Nat) :
    play (fuel + 2) (DIMCID k) TitForTatBot = some .C := by
  show (if proofSearch k
            ((Formula.impl (.plays .self .opp Action.C) (.plays .opp .self Action.D)).subst
              (DIMCID k) TitForTatBot)
          then eval (fuel + 1) (DIMCID k) TitForTatBot (.const Action.D)
          else eval (fuel + 1) (DIMCID k) TitForTatBot (.const Action.C)) = some .C
  rw [dimcidTFT_proofSearch_false k]; simp [eval]

theorem llm_outcome_DIMCID_vs_TitForTatBot :
    ∃ k₂, ∀ k, k₂ < k →
      ∃ fuel, outcome fuel (DIMCID k) TitForTatBot = some (.C, .C) := by
  refine ⟨0, fun k _ => ⟨4, ?_⟩⟩
  have hA : play 4 (DIMCID k) TitForTatBot = some .C := by
    simpa using DIMCID_plays_C_against_TitForTatBot k 2
  have hB : play 4 TitForTatBot (DIMCID k) = some .C := by
    simpa using TitForTatBot_plays_C_against_DIMCID k 0
  exact outcome_of_plays _ _ _ _ _ hA hB

end PD.Theorems
