import PrisonersDilemma.Program
import PrisonersDilemma.Dynamics
import PrisonersDilemma.BaseTheorems
import PrisonersDilemma.Base.Asymptotics
import PrisonersDilemma.Base.Helpers

import PrisonersDilemma.Bots.LlmGenerations.CIMCIC
import PrisonersDilemma.Bots.CupodTrollBot
import PrisonersDilemma.Theorems.CupodTrollBot.Helpers

open PD
open PD.BaseTheorems
open PD.Bots
namespace PD.Theorems

theorem cimcic_ctb_guard_unprovable_tail (k : Nat) :
    ∀ K φ, Pf K φ → K ≤ k →
      TailTo (.plays (CupodTrollBot k) (CIMCIC k) .C) φ → False := by
  intro K φ hp hK htail
  refine no_provable_tailToS_floor k
    (· = .plays (CupodTrollBot k) (CIMCIC k) .C)
    ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_
    K φ hp hK ((TailToS_singleton _ φ).2 htail)
  · rintro φ' rfl; exact ⟨_, _, _, rfl⟩
  · rintro K' hK' φ' rfl hA
    cases hA with
    | mk hpp hn =>
      unfold CupodTrollBot at hpp
      cases hpp with
      | search_t hProv hbr =>
          have : (Formula.eq (CIMCIC k) (CupodBot k)).interp := by
            have := Pf_sound _ _ hProv
            simpa [Formula.subst] using this
          simp only [Formula.interp] at this
          simp [CIMCIC, CupodBot] at this
      | search_f hneg hbr =>
          cases hbr
          simp only [c_leaf, c_node] at hn
          omega
  · intro me oppo c hS g ψ b hme
    injection hS with h1 h2 h3
    subst h1; subst h3
    unfold CupodTrollBot at hme
    simp only [Prog.search.injEq] at hme
    exact absurd hme.2.2.1 (by decide)
  · intro me oppo c hS p q hme
    injection hS with h1 h2 h3
    subst h1
    unfold CupodTrollBot at hme
    simp at hme
  · intro me oppo c hS p q hme
    injection hS with h1 h2 h3
    subst h1
    unfold CupodTrollBot at hme
    simp at hme
  · intro me oppo c hS g ψ b hme
    injection hS with h1 h2 h3
    subst h1
    unfold CupodTrollBot at hme
    simp at hme
  · intro z a' g ψ c0 c1 q oppo hS
    exfalso
    unfold CupodTrollBot at hS
    injection hS with h1 h2 h3
    simp at h1
  · intro me oppo c hS k₁ ψ₁ k₂ ψ₂ c1 q hme
    injection hS with h1 h2 h3
    subst h1
    unfold CupodTrollBot at hme
    simp at hme
  · intro me oppo c hS L hme
    injection hS with h1 h2 h3
    subst h1; subst h3
    unfold CupodTrollBot at hme
    cases L with
    | nil => simp [searchPlug] at hme
    | cons hd tl =>
        obtain ⟨g, ψ, e⟩ := hd
        simp only [searchPlug, Prog.search.injEq] at hme
        rcases hme with ⟨-, -, hbr, -⟩
        cases tl with
        | nil => simp [searchPlug] at hbr
        | cons hd2 tl2 => obtain ⟨g2, ψ2, e2⟩ := hd2; simp [searchPlug] at hbr
  · intro me oppo c hS hd L hme
    injection hS with h1 h2 h3
    subst h1; subst h3
    exfalso
    unfold CupodTrollBot at hme
    cases hd with
    | searchL g ψ e =>
        simp only [ctxPlug, Prog.search.injEq] at hme
        rcases hme with ⟨-, -, hbr, -⟩
        cases L with
        | nil => simp [ctxPlug] at hbr
        | cons hd2 tl2 =>
            cases hd2 with
            | searchL g2 ψ2 e2 => simp [ctxPlug] at hbr
            | iteL z2 aT2 other2 => simp [ctxPlug] at hbr
    | iteL z aT other => simp [ctxPlug] at hme

/-- CIMCIC's guard against CupodTrollBot is unprovable at its own budget `k`. -/
theorem proofSearch_false_CIMCIC_vs_CupodTrollBot (k : Nat) :
    proofSearch k
      ((Formula.impl (.plays .self .opp Action.C) (.plays .opp .self Action.C)).subst
        (CIMCIC k) (CupodTrollBot k)) = false := by
  cases hps : proofSearch k
      ((Formula.impl (.plays .self .opp Action.C) (.plays .opp .self Action.C)).subst
        (CIMCIC k) (CupodTrollBot k)) with
  | false => rfl
  | true =>
      exfalso
      have hpf : Pf k
          (Formula.impl (.plays (CIMCIC k) (CupodTrollBot k) Action.C)
                        (.plays (CupodTrollBot k) (CIMCIC k) Action.C)) := by
        have := (proofSearch_spec _ _).1 hps
        simpa [Formula.subst] using this
      refine cimcic_ctb_guard_unprovable_tail k k _ hpf (Nat.le_refl _) ?_
      refine ⟨rfl, ?_⟩
      intro hA
      simp only [TailTo] at hA
      injection hA with h1 h2 h3
      exact absurd h1 (by simp [CIMCIC, CupodTrollBot])

/-- CIMCIC defects against CupodTrollBot: the guard fails (unprovable), so it takes
    the `.const .D` branch. -/
theorem CIMCIC_plays_D_against_CupodTrollBot (k fuel : Nat) :
    play (fuel + 2) (CIMCIC k) (CupodTrollBot k) = some .D := by
  have hg := proofSearch_false_CIMCIC_vs_CupodTrollBot k
  show (if proofSearch k
            ((Formula.impl (.plays .self .opp Action.C) (.plays .opp .self Action.C)).subst
              (CIMCIC k) (CupodTrollBot k))
          then eval (fuel + 1) (CIMCIC k) (CupodTrollBot k) (.const Action.C)
          else eval (fuel + 1) (CIMCIC k) (CupodTrollBot k) (.const Action.D)) = some .D
  rw [hg]; simp [eval]

theorem llm_outcome_CIMCIC_vs_CupodTrollBot :
    ∃ k₂, ∀ k, k₂ < k →
      ∃ fuel, outcome fuel (CIMCIC k) (CupodTrollBot k) = some (.D, .C) := by
  refine ⟨0, fun k _ => ⟨2, ?_⟩⟩
  have hA : play 2 (CIMCIC k) (CupodTrollBot k) = some .D :=
    CIMCIC_plays_D_against_CupodTrollBot k 0
  have hB : play 2 (CupodTrollBot k) (CIMCIC k) = some .C :=
    CupodTrollBot_cooperates_if_opp_not_CupodBot k 0 (CIMCIC k)
      (by simp [CIMCIC, CupodBot])
  exact outcome_of_plays _ _ _ _ _ hA hB

end PD.Theorems
