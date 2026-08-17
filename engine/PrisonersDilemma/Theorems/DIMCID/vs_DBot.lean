import PrisonersDilemma.Bots.LlmGenerations.DIMCID
import PrisonersDilemma.Bots.DBot
import PrisonersDilemma.Bots.DefectBot
import PrisonersDilemma.Dynamics
import PrisonersDilemma.Base.Helpers
import PrisonersDilemma.BaseTheorems
import PrisonersDilemma.Base.Asymptotics
import PrisonersDilemma.Theorems.DefectBot.Helpers

open PD
open PD.BaseTheorems
open PD.Bots
namespace PD.Theorems

/-- Abbreviation for the threshold predicate: k is large enough that DIMCID's guard
    against `.bot DefectBot` is provable within budget k. -/
abbrev dimcidThresh (k : Nat) : Prop :=
  2 + (Formula.impl (.plays (DIMCID k) (.bot DefectBot) Action.C)
        (.plays (.bot DefectBot) (DIMCID k) Action.D)).size ≤ k

-- === Part A: DIMCID defects against `.bot DefectBot` ===

theorem dimcid_guard_bot_def_provable (k : Nat) :
    Pf (2 + (Formula.impl (.plays (DIMCID k) (.bot DefectBot) Action.C)
              (.plays (.bot DefectBot) (DIMCID k) Action.D)).size)
      (.impl (.plays (DIMCID k) (.bot DefectBot) Action.C)
             (.plays (.bot DefectBot) (DIMCID k) Action.D)) := by
  have hcons : Pf 2 (.plays (.bot DefectBot) (DIMCID k) Action.D) :=
    Pf.atom ⟨PlaysProof.bot PlaysProof.const, by decide⟩
  exact Pf.weakenImpl _ _ 2 hcons (by omega)

theorem proofSearch_true_bot_def (k : Nat) (hk : dimcidThresh k) :
    proofSearch k
      ((Formula.impl (.plays .self .opp Action.C) (.plays .opp .self Action.D)).subst
        (DIMCID k) (.bot DefectBot)) = true := by
  show proofSearch k
      (.impl (.plays (DIMCID k) (.bot DefectBot) Action.C)
             (.plays (.bot DefectBot) (DIMCID k) Action.D)) = true
  exact (proofSearch_spec k _).2 (Pf_mono (dimcid_guard_bot_def_provable k) hk)

theorem DIMCID_plays_D_bot_def (k fuel : Nat) (hk : dimcidThresh k) :
    play (fuel + 2) (DIMCID k) (.bot DefectBot) = some .D := by
  have hg := proofSearch_true_bot_def k hk
  show (if proofSearch k
            ((Formula.impl (.plays .self .opp Action.C) (.plays .opp .self Action.D)).subst
              (DIMCID k) (.bot DefectBot))
          then eval (fuel + 1) (DIMCID k) (.bot DefectBot) (.const Action.D)
          else eval (fuel + 1) (DIMCID k) (.bot DefectBot) (.const Action.C)) = some .D
  rw [hg]; simp [eval]

-- === Part B: DBot cooperates with DIMCID ===

theorem DBot_plays_C_against_DIMCID (k fuel : Nat) (hk : dimcidThresh k) :
    play (fuel + 4) DBot (DIMCID k) = some .C := by
  have hDimcid : play (fuel + 2) (DIMCID k) (.bot DefectBot) = some .D :=
    DIMCID_plays_D_bot_def k fuel hk
  have hGuard :
      eval (fuel + 3) DBot (DIMCID k) (.sim .opp (.bot DefectBot)) = some .D := by
    simpa [Nat.add_assoc] using
      (eval_sim_opp_bot_of_play (fuel + 2) DBot (DIMCID k) DefectBot Action.D hDimcid)
  have hPlay := play_ite_from_guard
    fuel 3 DBot (DIMCID k) (.sim .opp (.bot DefectBot))
    (.const Action.D) (.const Action.C)
    Action.C Action.D
    (by rfl) hGuard
  simpa [eval] using hPlay

theorem interp_DBot_D_vs_DIMCID_false (k : Nat) (hk : dimcidThresh k) :
    ¬ (Formula.plays DBot (DIMCID k) Action.D).interp := by
  rintro ⟨n, hn⟩
  have hC : play (n + 4) DBot (DIMCID k) = some .C := DBot_plays_C_against_DIMCID k n hk
  have hD : play (n + 4) DBot (DIMCID k) = some .D := by
    unfold play at hn ⊢; exact eval_mono_le hn (n + 4) (by omega)
  rw [hC] at hD; cases hD

theorem interp_DIMCID_C_vs_botDef_false (k : Nat) (hk : dimcidThresh k) :
    ¬ (Formula.plays (DIMCID k) (.bot DefectBot) Action.C).interp := by
  rintro ⟨n, hn⟩
  have hD : play (n + 2) (DIMCID k) (.bot DefectBot) = some .D := DIMCID_plays_D_bot_def k n hk
  have hC : play (n + 2) (DIMCID k) (.bot DefectBot) = some .C := by
    unfold play at hn ⊢; exact eval_mono_le hn (n + 2) (by omega)
  rw [hD] at hC; cases hC

-- === Part C: the guard DIMCID checks against DBot is unprovable ===

theorem dimcid_guard_dbot_not_provable (k : Nat) (hk : dimcidThresh k) :
    ¬ Pf k (.impl (.plays (DIMCID k) DBot Action.C) (.plays DBot (DIMCID k) Action.D)) := by
  intro hp
  set S : Formula → Prop := fun φ =>
    φ = .plays DBot (DIMCID k) Action.D ∨
    φ = .plays (DIMCID k) (.bot DefectBot) Action.C with hS
  refine no_provable_tailToS_floor k S ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_
    k _ hp le_rfl ?_
  · rintro φ (rfl | rfl)
    · exact ⟨_, _, _, rfl⟩
    · exact ⟨_, _, _, rfl⟩
  · rintro K hK φ (rfl | rfl) hA
    · exact interp_DBot_D_vs_DIMCID_false k hk (AtomProvable_sound K _ hA)
    · exact interp_DIMCID_C_vs_botDef_false k hk (AtomProvable_sound K _ hA)
  · rintro me oppo c (h | h) g ψ b hme <;> injection h with h1 h2 h3 <;> subst h1 <;>
      subst h3 <;> simp [DBot, DIMCID] at hme
  · rintro me oppo c (h | h) p q hme <;> injection h with h1 h2 h3 <;> subst h1 <;>
      subst h3 <;> simp [DBot, DIMCID] at hme
  · rintro me oppo c (h | h) p q hme <;> injection h with h1 h2 h3 <;> subst h1 <;>
      subst h3 <;> simp [DBot, DIMCID] at hme
  · rintro me oppo c (h | h) g ψ b hme <;> injection h with h1 h2 h3 <;> subst h1 <;>
      subst h3 <;> simp [DBot, DIMCID] at hme
  · rintro z a' g ψ c0 c1 q oppo (h | h) <;> injection h with h1 h2 h3 <;>
      simp [DBot, DIMCID] at h1
  · rintro me oppo c (h | h) k₁ ψ₁ k₂ ψ₂ c1 q hme <;> injection h with h1 h2 h3 <;>
      subst h1 <;> subst h3 <;> simp [DBot, DIMCID] at hme
  · rintro me oppo c (h | h) L hme
    · injection h with h1 h2 h3; subst h1; subst h3
      cases L with
      | nil => simp [searchPlug, DBot] at hme
      | cons hd tl => obtain ⟨g, ψ, e⟩ := hd; simp [searchPlug, DBot] at hme
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
    · injection h with h1 h2 h3; subst h1; subst h2; subst h3
      cases hd with
      | searchL g ψ e => simp [ctxPlug, DBot] at hme
      | iteL z aT other =>
          simp only [ctxPlug, DBot, Prog.ite.injEq, Prog.sim.injEq, Prog.bot.injEq] at hme
          obtain ⟨⟨_, rfl⟩, rfl, hplug, rfl⟩ := hme
          cases L with
          | nil =>
              refine ⟨.plays (DIMCID k) (.bot DefectBot) Action.C, ?_, Or.inr rfl⟩
              simp [ctxGuards, ctxGuard]
          | cons hd2 tl2 =>
              cases hd2 <;> simp [ctxPlug] at hplug
    · injection h with h1 h2 h3; subst h1; subst h2; subst h3
      cases hd with
      | searchL g ψ e =>
          simp only [ctxPlug, DIMCID, Prog.search.injEq] at hme
          obtain ⟨rfl, rfl, hplug, rfl⟩ := hme
          cases L with
          | nil => simp [ctxPlug] at hplug
          | cons hd2 tl2 => cases hd2 <;> simp [ctxPlug] at hplug
      | iteL z aT other => simp [ctxPlug, DIMCID] at hme
  · -- polarity plug: DBot is an `.ite` (never a `plug2`), and DIMCID's guard is an
    -- `.impl` (no `elseL` match) with then-slot `.const D ≠` any C-plug
    rintro me oppo c (h | h) hd L hme
    · injection h with h1 h2 h3; subst h1; subst h3
      exfalso
      cases hd <;> simp [plug2, DBot] at hme
    · injection h with h1 h2 h3; subst h1; subst h3
      exfalso
      cases hd with
      | thenL g ψ e =>
          simp only [plug2, DIMCID, Prog.search.injEq] at hme
          obtain ⟨-, -, hplug, -⟩ := hme
          cases L with
          | nil => simp [plug2] at hplug
          | cons hd2 tl2 => cases hd2 <;> simp [plug2] at hplug
      | elseL g P' Q' c' q =>
          simp only [plug2, DIMCID, Prog.search.injEq] at hme
          exact absurd hme.2.1 (by simp)
  · refine ⟨Or.inl rfl, ?_⟩
    intro hcontra
    simp only [hS] at hcontra
    rcases hcontra with h | h <;> simp [DBot, DIMCID] at h

theorem proofSearch_false_dbot (k : Nat) (hk : dimcidThresh k) :
    proofSearch k
      ((Formula.impl (.plays .self .opp Action.C) (.plays .opp .self Action.D)).subst
        (DIMCID k) DBot) = false := by
  show proofSearch k
      (.impl (.plays (DIMCID k) DBot Action.C) (.plays DBot (DIMCID k) Action.D)) = false
  cases hps : proofSearch k
      (.impl (.plays (DIMCID k) DBot Action.C) (.plays DBot (DIMCID k) Action.D)) with
  | false => rfl
  | true => exact absurd ((proofSearch_spec k _).1 hps) (dimcid_guard_dbot_not_provable k hk)

theorem DIMCID_plays_C_against_DBot (k fuel : Nat) (hk : dimcidThresh k) :
    play (fuel + 2) (DIMCID k) DBot = some .C := by
  have hg := proofSearch_false_dbot k hk
  show (if proofSearch k
            ((Formula.impl (.plays .self .opp Action.C) (.plays .opp .self Action.D)).subst
              (DIMCID k) DBot)
          then eval (fuel + 1) (DIMCID k) DBot (.const Action.D)
          else eval (fuel + 1) (DIMCID k) DBot (.const Action.C)) = some .C
  rw [hg]; simp [eval]

-- === Final theorem ===

theorem llm_outcome_DIMCID_vs_DBot :
    ∃ k₂, ∀ k, k₂ < k →
      ∃ fuel, outcome fuel (DIMCID k) DBot = some (.C, .C) := by
  obtain ⟨K, hK⟩ := linear_log2_add_le 4 100
  refine ⟨K, fun k hk => ⟨7, ?_⟩⟩
  have hthresh : dimcidThresh k := by
    have hsz : 2 + (Formula.impl (.plays (DIMCID k) (.bot DefectBot) Action.C)
                (.plays (.bot DefectBot) (DIMCID k) Action.D)).size
              ≤ 4 * Nat.log2 k + 100 := by
      simp only [DIMCID, DefectBot, Formula.size, Prog.size, numCost]; omega
    have hkK : 4 * Nat.log2 k + 100 ≤ k := hK k (by omega)
    show 2 + _ ≤ k
    omega
  have hA : play 7 (DIMCID k) DBot = some .C := by
    simpa using DIMCID_plays_C_against_DBot k 5 hthresh
  have hB : play 7 DBot (DIMCID k) = some .C := by
    simpa using DBot_plays_C_against_DIMCID k 3 hthresh
  exact outcome_of_plays _ _ _ _ _ hA hB

end PD.Theorems
