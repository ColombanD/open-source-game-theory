import PrisonersDilemma.Bots.LlmGenerations.DIMCID
import PrisonersDilemma.Bots.EBot
import PrisonersDilemma.Bots.CooperateBot
import PrisonersDilemma.Bots.DefectBot
import PrisonersDilemma.Bots.MirrorBot
import PrisonersDilemma.Dynamics
import PrisonersDilemma.Base.Helpers
import PrisonersDilemma.BaseTheorems
import PrisonersDilemma.Base.Asymptotics
import PrisonersDilemma.Theorems.CooperateBot.Helpers
import PrisonersDilemma.Theorems.DefectBot.Helpers

open PD
open PD.BaseTheorems
open PD.Bots
namespace PD.Theorems

/-- Threshold: k is large enough for DIMCID's guard vs `.bot DefectBot` to be provable. -/
abbrev dimcidE_thresh (k : Nat) : Prop :=
  2 + (Formula.impl (.plays (DIMCID k) (.bot DefectBot) Action.C)
        (.plays (.bot DefectBot) (DIMCID k) Action.D)).size ≤ k

-- === Part A: DIMCID defects against `.bot DefectBot` ===

theorem dimcidE_guard_bot_def_provable (k : Nat) :
    Pf (2 + (Formula.impl (.plays (DIMCID k) (.bot DefectBot) Action.C)
              (.plays (.bot DefectBot) (DIMCID k) Action.D)).size)
      (.impl (.plays (DIMCID k) (.bot DefectBot) Action.C)
             (.plays (.bot DefectBot) (DIMCID k) Action.D)) := by
  have hcons : Pf 2 (.plays (.bot DefectBot) (DIMCID k) Action.D) :=
    Pf.atom ⟨PlaysProof.bot PlaysProof.const, by decide⟩
  exact Pf.weakenImpl _ _ 2 hcons (by omega)

theorem proofSearch_true_botdef_E (k : Nat) (hk : dimcidE_thresh k) :
    proofSearch k
      ((Formula.impl (.plays .self .opp Action.C) (.plays .opp .self Action.D)).subst
        (DIMCID k) (.bot DefectBot)) = true := by
  show proofSearch k
      (.impl (.plays (DIMCID k) (.bot DefectBot) Action.C)
             (.plays (.bot DefectBot) (DIMCID k) Action.D)) = true
  exact (proofSearch_spec k _).2 (Pf_mono (dimcidE_guard_bot_def_provable k) hk)

theorem DIMCID_plays_D_botdef_E (k fuel : Nat) (hk : dimcidE_thresh k) :
    play (fuel + 2) (DIMCID k) (.bot DefectBot) = some .D := by
  have hg := proofSearch_true_botdef_E k hk
  show (if proofSearch k
            ((Formula.impl (.plays .self .opp Action.C) (.plays .opp .self Action.D)).subst
              (DIMCID k) (.bot DefectBot))
          then eval (fuel + 1) (DIMCID k) (.bot DefectBot) (.const Action.D)
          else eval (fuel + 1) (DIMCID k) (.bot DefectBot) (.const Action.C)) = some .D
  rw [hg]; simp [eval]

-- === Part B: DIMCID cooperates against `.bot CooperateBot` ===

theorem dimcidE_consequent_botcoop_not_provable (k m : Nat) :
    ¬ Pf m (.plays (.bot CooperateBot) (DIMCID k) Action.D) := by
  intro h
  exact absurd (Pf_sound m _ h) (interp_bot_CooperateBot_plays_D_false (DIMCID k))

theorem dimcidE_no_provable_botcoop (k : Nat) :
    ∀ {m : Nat} {φ : Formula}, Pf m φ →
      ¬ TailTo (.plays (.bot CooperateBot) (DIMCID k) Action.D) φ :=
  no_provable_tailTo_unreadable _ _ _
    (fun n hA => dimcidE_consequent_botcoop_not_provable k n (.atom hA))
    (by rintro (⟨_, _, _, _, h⟩ | ⟨_, _, h⟩ | ⟨_, _, h⟩ | ⟨_, _, _, _, h⟩ |
          ⟨_, _, _, _, _, _, _, h⟩ | ⟨_, _, _, _, _, _, _, h⟩) <;> simp [CooperateBot] at h)
    (by intro L h
        cases L with
        | nil => simp [searchPlug, CooperateBot] at h
        | cons hd tl =>
            obtain ⟨g, ψ, e⟩ := hd
            simp [searchPlug, CooperateBot] at h)
    (by intro hd L h
        cases hd with
        | searchL g' ψ' e' => simp [ctxPlug, CooperateBot] at h
        | iteL z' aT' other' => simp [ctxPlug, CooperateBot] at h)

theorem dimcidE_guard_botcoop_not_provable (k : Nat) :
    ¬ Pf k (.impl (.plays (DIMCID k) (.bot CooperateBot) Action.C)
                  (.plays (.bot CooperateBot) (DIMCID k) Action.D)) := by
  intro h
  refine dimcidE_no_provable_botcoop k h ?_
  exact ⟨rfl, by simp [DIMCID, CooperateBot]⟩

theorem proofSearch_false_botcoop_E (k : Nat) :
    proofSearch k
      ((Formula.impl (.plays .self .opp Action.C) (.plays .opp .self Action.D)).subst
        (DIMCID k) (.bot CooperateBot)) = false := by
  show proofSearch k
      (.impl (.plays (DIMCID k) (.bot CooperateBot) Action.C)
             (.plays (.bot CooperateBot) (DIMCID k) Action.D)) = false
  cases hps : proofSearch k
      (.impl (.plays (DIMCID k) (.bot CooperateBot) Action.C)
             (.plays (.bot CooperateBot) (DIMCID k) Action.D)) with
  | false => rfl
  | true => exact absurd ((proofSearch_spec k _).1 hps) (dimcidE_guard_botcoop_not_provable k)

theorem DIMCID_plays_C_botcoop_E (k fuel : Nat) :
    play (fuel + 2) (DIMCID k) (.bot CooperateBot) = some .C := by
  have hg := proofSearch_false_botcoop_E k
  show (if proofSearch k
            ((Formula.impl (.plays .self .opp Action.C) (.plays .opp .self Action.D)).subst
              (DIMCID k) (.bot CooperateBot))
          then eval (fuel + 1) (DIMCID k) (.bot CooperateBot) (.const Action.D)
          else eval (fuel + 1) (DIMCID k) (.bot CooperateBot) (.const Action.C)) = some .C
  rw [hg]; simp [eval]

-- === Part C: EBot plays C against DIMCID ===

theorem EBot_plays_C_against_DIMCID (k fuel : Nat) (hk : dimcidE_thresh k) :
    play (fuel + 5) EBot (DIMCID k) = some .C := by
  have hProbe1 : play (fuel + 3) (DIMCID k) (.bot DefectBot) = some .D := by
    simpa [Nat.add_assoc] using DIMCID_plays_D_botdef_E k (fuel + 1) hk
  have hGuard1 :
      eval (fuel + 4) EBot (DIMCID k) (.sim .opp (.bot DefectBot)) = some .D := by
    simpa [Nat.add_assoc] using
      (eval_sim_opp_bot_of_play (fuel + 3) EBot (DIMCID k) DefectBot Action.D hProbe1)
  have hProbe2 : play (fuel + 2) (DIMCID k) (.bot CooperateBot) = some .C :=
    DIMCID_plays_C_botcoop_E k fuel
  have hGuard2 :
      eval (fuel + 3) EBot (DIMCID k) (.sim .opp (.bot CooperateBot)) = some .C := by
    simpa [Nat.add_assoc] using
      (eval_sim_opp_bot_of_play (fuel + 2) EBot (DIMCID k) CooperateBot Action.C hProbe2)
  have hInner :
      eval (fuel + 4) EBot (DIMCID k)
        (.ite (.sim .opp (.bot CooperateBot)) Action.C (.const Action.C)
          (.ite (.sim .opp (.bot MirrorBot)) Action.C (.const Action.C) (.const Action.D))) =
        some .C := by
    simpa [Nat.add_assoc] using
      (eval_ite_from_guard (fuel + 3) EBot (DIMCID k)
        (.sim .opp (.bot CooperateBot)) (.const Action.C)
        (.ite (.sim .opp (.bot MirrorBot)) Action.C (.const Action.C) (.const Action.D))
        Action.C Action.C hGuard2)
  have hPlay := play_ite_from_guard
    fuel 4 EBot (DIMCID k) (.sim .opp (.bot DefectBot))
    (.const Action.D)
    (.ite (.sim .opp (.bot CooperateBot)) Action.C (.const Action.C)
      (.ite (.sim .opp (.bot MirrorBot)) Action.C (.const Action.C) (.const Action.D)))
    Action.C Action.D
    (by rfl) hGuard1
  simpa [Nat.add_assoc, hInner] using hPlay

-- === Part D: DIMCID cooperates against EBot (guard unprovable) ===

theorem interp_EBot_D_vs_DIMCID_false (k : Nat) (hk : dimcidE_thresh k) :
    ¬ (Formula.plays EBot (DIMCID k) Action.D).interp := by
  rintro ⟨n, hn⟩
  have hC : play (n + 5) EBot (DIMCID k) = some .C := EBot_plays_C_against_DIMCID k n hk
  have hD : play (n + 5) EBot (DIMCID k) = some .D := by
    unfold play at hn ⊢; exact eval_mono_le hn (n + 5) (by omega)
  rw [hC] at hD; cases hD

theorem interp_DIMCID_C_vs_botdef_false (k : Nat) (hk : dimcidE_thresh k) :
    ¬ (Formula.plays (DIMCID k) (.bot DefectBot) Action.C).interp := by
  rintro ⟨n, hn⟩
  have hD : play (n + 2) (DIMCID k) (.bot DefectBot) = some .D := DIMCID_plays_D_botdef_E k n hk
  have hC : play (n + 2) (DIMCID k) (.bot DefectBot) = some .C := by
    unfold play at hn ⊢; exact eval_mono_le hn (n + 2) (by omega)
  rw [hD] at hC; cases hC

theorem dimcidE_guard_ebot_not_provable (k : Nat) (hk : dimcidE_thresh k) :
    ¬ Pf k (.impl (.plays (DIMCID k) EBot Action.C) (.plays EBot (DIMCID k) Action.D)) := by
  intro hp
  set S : Formula → Prop := fun φ =>
    φ = .plays EBot (DIMCID k) Action.D ∨
    φ = .plays (DIMCID k) (.bot DefectBot) Action.C with hS
  refine no_provable_tailToS_floor k S ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_
    k _ hp le_rfl ?_
  · rintro φ (rfl | rfl)
    · exact ⟨_, _, _, rfl⟩
    · exact ⟨_, _, _, rfl⟩
  · rintro K hK φ (rfl | rfl) hA
    · exact interp_EBot_D_vs_DIMCID_false k hk (AtomProvable_sound K _ hA)
    · exact interp_DIMCID_C_vs_botdef_false k hk (AtomProvable_sound K _ hA)
  · rintro me oppo c (h | h) g ψ b hme <;> injection h with h1 h2 h3 <;> subst h1 <;>
      subst h3 <;> simp [EBot, DIMCID] at hme
  · rintro me oppo c (h | h) p q hme <;> injection h with h1 h2 h3 <;> subst h1 <;>
      subst h3 <;> simp [EBot, DIMCID] at hme
  · rintro me oppo c (h | h) p q hme <;> injection h with h1 h2 h3 <;> subst h1 <;>
      subst h3 <;> simp [EBot, DIMCID] at hme
  · rintro me oppo c (h | h) g ψ b hme <;> injection h with h1 h2 h3 <;> subst h1 <;>
      subst h3 <;> simp [EBot, DIMCID] at hme
  · rintro z a' g ψ c0 c1 q oppo (h | h) <;> injection h with h1 h2 h3 <;>
      simp [EBot, DIMCID] at h1
  · rintro me oppo c (h | h) k₁ ψ₁ k₂ ψ₂ c1 q hme <;> injection h with h1 h2 h3 <;>
      subst h1 <;> subst h3 <;> simp [EBot, DIMCID] at hme
  · rintro me oppo c (h | h) L hme
    · injection h with h1 h2 h3; subst h1; subst h3
      cases L with
      | nil => simp [searchPlug, EBot] at hme
      | cons hd tl => obtain ⟨g, ψ, e⟩ := hd; simp [searchPlug, EBot] at hme
    · injection h with h1 h2 h3; subst h1; subst h3
      cases L with
      | nil => simp [searchPlug, DIMCID] at hme
      | cons hd tl =>
          obtain ⟨g, ψ, e⟩ := hd
          simp only [searchPlug, DIMCID, Prog.search.injEq] at hme
          cases tl with
          | nil => simp [searchPlug] at hme
          | cons hd2 tl2 => obtain ⟨g2, ψ2, e2⟩ := hd2; simp [searchPlug] at hme
  · rintro me oppo c (h | h) hd L hme
    · injection h with h1 h2 h3; subst h1; subst h3
      cases hd with
      | searchL g ψ e => simp [ctxPlug, EBot] at hme
      | iteL z aT other =>
          simp only [ctxPlug, EBot, Prog.ite.injEq, Prog.sim.injEq, Prog.bot.injEq] at hme
          obtain ⟨⟨_, rfl⟩, rfl, hplug, rfl⟩ := hme
          subst h2
          cases L with
          | nil =>
              refine ⟨.plays (DIMCID k) (.bot DefectBot) Action.C, ?_, Or.inr rfl⟩
              simp [ctxGuards, ctxGuard]
          | cons hd2 tl2 =>
              cases hd2 <;> simp [ctxPlug] at hplug
    · injection h with h1 h2 h3; subst h1; subst h3
      cases hd with
      | searchL g ψ e =>
          simp only [ctxPlug, DIMCID, Prog.search.injEq] at hme
          obtain ⟨rfl, rfl, hplug, rfl⟩ := hme
          cases L with
          | nil => simp [ctxPlug] at hplug
          | cons hd2 tl2 => cases hd2 <;> simp [ctxPlug] at hplug
      | iteL z aT other => simp [ctxPlug, DIMCID] at hme
  · refine ⟨Or.inl rfl, ?_⟩
    intro hcontra
    simp only [hS] at hcontra
    rcases hcontra with h | h <;> simp [EBot, DIMCID] at h

theorem proofSearch_false_ebot_E (k : Nat) (hk : dimcidE_thresh k) :
    proofSearch k
      ((Formula.impl (.plays .self .opp Action.C) (.plays .opp .self Action.D)).subst
        (DIMCID k) EBot) = false := by
  show proofSearch k
      (.impl (.plays (DIMCID k) EBot Action.C) (.plays EBot (DIMCID k) Action.D)) = false
  cases hps : proofSearch k
      (.impl (.plays (DIMCID k) EBot Action.C) (.plays EBot (DIMCID k) Action.D)) with
  | false => rfl
  | true => exact absurd ((proofSearch_spec k _).1 hps) (dimcidE_guard_ebot_not_provable k hk)

theorem DIMCID_plays_C_against_EBot (k fuel : Nat) (hk : dimcidE_thresh k) :
    play (fuel + 2) (DIMCID k) EBot = some .C := by
  have hg := proofSearch_false_ebot_E k hk
  show (if proofSearch k
            ((Formula.impl (.plays .self .opp Action.C) (.plays .opp .self Action.D)).subst
              (DIMCID k) EBot)
          then eval (fuel + 1) (DIMCID k) EBot (.const Action.D)
          else eval (fuel + 1) (DIMCID k) EBot (.const Action.C)) = some .C
  rw [hg]; simp [eval]

-- === Final theorem ===

theorem llm_outcome_DIMCID_vs_EBot :
    ∃ k₂, ∀ k, k₂ < k →
      ∃ fuel, outcome fuel (DIMCID k) EBot = some (.C, .C) := by
  obtain ⟨K, hK⟩ := linear_log2_add_le 4 100
  refine ⟨K, fun k hk => ⟨7, ?_⟩⟩
  have hthresh : dimcidE_thresh k := by
    have hsz : 2 + (Formula.impl (.plays (DIMCID k) (.bot DefectBot) Action.C)
                (.plays (.bot DefectBot) (DIMCID k) Action.D)).size
              ≤ 4 * Nat.log2 k + 100 := by
      simp only [DIMCID, DefectBot, Formula.size, Prog.size, numCost]; omega
    have hkK : 4 * Nat.log2 k + 100 ≤ k := hK k (by omega)
    show 2 + _ ≤ k
    omega
  have hA : play 7 (DIMCID k) EBot = some .C := by
    simpa using DIMCID_plays_C_against_EBot k 5 hthresh
  have hB : play 7 EBot (DIMCID k) = some .C := by
    simpa using EBot_plays_C_against_DIMCID k 2 hthresh
  exact outcome_of_plays _ _ _ _ _ hA hB

end PD.Theorems
