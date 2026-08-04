import PrisonersDilemma.Program
import PrisonersDilemma.Dynamics
import PrisonersDilemma.BaseTheorems
import PrisonersDilemma.Base.Asymptotics
import PrisonersDilemma.Base.Helpers

import PrisonersDilemma.Bots.LlmGenerations.CIMCIC
import PrisonersDilemma.Bots.LlmGenerations.PrudentBot
import PrisonersDilemma.Bots.DefectBot
import PrisonersDilemma.Theorems.DefectBot.Helpers
import PrisonersDilemma.Theorems.PrudentBot.Helpers

open PD
open PD.BaseTheorems
open PD.Bots
namespace PD.Theorems

/-! # CIMCIC vs PrudentBot → (D, D) at every budget (large-`k` threshold).

Same-`k` self-referential deadlock. PrudentBot's prudence check about CIMCIC
("CIMCIC defects vs `.bot DefectBot`") is CIMCIC's own budget-`k` else-play — its
certificate pays the `search_f` floor `k`, unaffordable at the same budget. So
PrudentBot cannot prove prudence and defects. With PrudentBot defecting, CIMCIC's
guard `(CIMCIC plays C vs PB) → (PB plays C vs CIMCIC)` has a FALSE consequent, and
by soundness it is unprovable (proving it would fire CIMCIC's search into
cooperation, which would make the consequent true — a contradiction). So CIMCIC
defects too. Mutual defection is the honest fixed point, exactly as with same-`k`
PrudentBot self-play. -/

theorem cimcic_pb_prudence_unprovable_tail (k : Nat) :
    ∀ K φ, Pf K φ → K ≤ k →
      TailTo (.plays (CIMCIC k) (.bot DefectBot) .D) φ → False := by
  intro K φ hp hK htail
  refine no_provable_tailToS_floor k
    (· = .plays (CIMCIC k) (.bot DefectBot) .D)
    ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_
    K φ hp hK ((TailToS_singleton _ φ).2 htail)
  · rintro φ' rfl; exact ⟨_, _, _, rfl⟩
  · rintro K' hK' φ' rfl hA
    cases hA with
    | mk hpp hn =>
      unfold CIMCIC at hpp
      cases hpp with
      | search_t hProv hbr => cases hbr
      | search_f hneg hbr =>
          cases hbr
          simp only [c_leaf, c_node] at hn
          omega
  · intro me oppo c hS g ψ b hme
    injection hS with h1 h2 h3
    subst h1; subst h3
    unfold CIMCIC at hme
    simp only [Prog.search.injEq] at hme
    exact absurd hme.2.2.1 (by decide)
  · intro me oppo c hS p q hme
    injection hS with h1 h2 h3
    subst h1
    unfold CIMCIC at hme
    simp at hme
  · intro me oppo c hS p q hme
    injection hS with h1 h2 h3
    subst h1
    unfold CIMCIC at hme
    simp at hme
  · intro me oppo c hS g ψ b hme
    injection hS with h1 h2 h3
    subst h1
    unfold CIMCIC at hme
    simp at hme
  · intro z a' g ψ c0 c1 q oppo hS
    exfalso
    unfold CIMCIC at hS
    injection hS with h1 h2 h3
    simp at h1
  · intro me oppo c hS k₁ ψ₁ k₂ ψ₂ c1 q hme
    injection hS with h1 h2 h3
    subst h1; subst h3
    unfold CIMCIC at hme
    simp at hme
  · intro me oppo c hS L hme
    injection hS with h1 h2 h3
    subst h1; subst h3
    unfold CIMCIC at hme
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
    unfold CIMCIC at hme
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
  · -- polarity plug: CIMCIC's guard is an `.impl` — no `elseL` layer can match it,
    -- and the then-slot holds `.const C ≠` any D-plug
    intro me oppo c hS hd L hme
    injection hS with h1 h2 h3
    subst h1; subst h3
    exfalso
    unfold CIMCIC at hme
    cases hd with
    | thenL g ψ e =>
        simp only [plug2, Prog.search.injEq] at hme
        obtain ⟨-, -, hplug, -⟩ := hme
        cases L with
        | nil => simp [plug2] at hplug
        | cons hd2 tl2 => cases hd2 <;> simp [plug2] at hplug
    | elseL g P' Q' c' q =>
        simp only [plug2, Prog.search.injEq] at hme
        exact absurd hme.2.1 (by simp)

theorem cimcic_pb_proofSearch_false_prudence (k : Nat) :
    proofSearch k (.plays (CIMCIC k) (.bot DefectBot) .D) = false := by
  cases h : proofSearch k (.plays (CIMCIC k) (.bot DefectBot) .D) with
  | true =>
      exact absurd ((proofSearch_spec k _).mp h)
        (fun hp => cimcic_pb_prudence_unprovable_tail k k _ hp le_rfl (by simp))
  | false => rfl

theorem PrudentBot_plays_D_against_CIMCIC (k fuel : Nat) :
    play (fuel + 3) (PrudentBot k) (CIMCIC k) = some .D := by
  cases h1 : proofSearch k (.plays (CIMCIC k) (PrudentBot k) .C) with
  | false =>
      simpa [Nat.add_assoc] using
        PrudentBot_plays_D_of_search_false k (fuel + 1) (CIMCIC k) h1
  | true =>
      exact prudent_eval_inner_false k fuel (CIMCIC k) h1
        (cimcic_pb_proofSearch_false_prudence k)

theorem cimcic_C_of_guard_vs_PB (k fuel : Nat)
    (hg : proofSearch k
        ((Formula.impl (.plays .self .opp Action.C) (.plays .opp .self Action.C)).subst
          (CIMCIC k) (PrudentBot k)) = true) :
    play (fuel + 2) (CIMCIC k) (PrudentBot k) = some .C := by
  show (if proofSearch k
            ((Formula.impl (.plays .self .opp Action.C) (.plays .opp .self Action.C)).subst
              (CIMCIC k) (PrudentBot k))
          then eval (fuel + 1) (CIMCIC k) (PrudentBot k) (.const Action.C)
          else eval (fuel + 1) (CIMCIC k) (PrudentBot k) (.const Action.D)) = some .C
  rw [hg]; simp [eval]

/-- PrudentBot never plays C against CIMCIC. -/
theorem cimcic_pb_PB_not_C (k : Nat) :
    ¬ (Formula.plays (PrudentBot k) (CIMCIC k) .C).interp := by
  rintro ⟨n, hn⟩
  have hD : play (n + 3) (PrudentBot k) (CIMCIC k) = some .D :=
    PrudentBot_plays_D_against_CIMCIC k n
  have hC : play (n + 3) (PrudentBot k) (CIMCIC k) = some .C := by
    unfold play at hn ⊢; exact eval_mono_le hn (n + 3) (by omega)
  rw [hC] at hD; cases hD

/-- CIMCIC's guard against PrudentBot is unprovable at budget `k`: if it were
    provable, CIMCIC would cooperate, forcing (via soundness of the guard) PrudentBot
    to cooperate — but PrudentBot defects. -/
theorem cimcic_pb_guard_false (k : Nat) :
    proofSearch k
      ((Formula.impl (.plays .self .opp Action.C) (.plays .opp .self Action.C)).subst
        (CIMCIC k) (PrudentBot k)) = false := by
  cases h : proofSearch k
      ((Formula.impl (.plays .self .opp Action.C) (.plays .opp .self Action.C)).subst
        (CIMCIC k) (PrudentBot k)) with
  | false => rfl
  | true =>
      exfalso
      -- CIMCIC cooperates
      have hCC : play 2 (CIMCIC k) (PrudentBot k) = some .C :=
        cimcic_C_of_guard_vs_PB k 0 h
      have hCimC : (Formula.plays (CIMCIC k) (PrudentBot k) .C).interp := ⟨2, hCC⟩
      -- the guard is sound
      have hpf : Pf k
          (Formula.impl (.plays (CIMCIC k) (PrudentBot k) Action.C)
                        (.plays (PrudentBot k) (CIMCIC k) Action.C)) := by
        have := (proofSearch_spec _ _).1 h
        simpa [Formula.subst] using this
      have hsound := Pf_sound _ _ hpf
      simp only [Formula.interp] at hsound
      exact cimcic_pb_PB_not_C k (hsound hCimC)

theorem CIMCIC_plays_D_against_PrudentBot (k fuel : Nat) :
    play (fuel + 2) (CIMCIC k) (PrudentBot k) = some .D := by
  show (if proofSearch k
            ((Formula.impl (.plays .self .opp Action.C) (.plays .opp .self Action.C)).subst
              (CIMCIC k) (PrudentBot k))
          then eval (fuel + 1) (CIMCIC k) (PrudentBot k) (.const Action.C)
          else eval (fuel + 1) (CIMCIC k) (PrudentBot k) (.const Action.D)) = some .D
  rw [cimcic_pb_guard_false k]; simp [eval]

/-- **CIMCIC vs PrudentBot → (D, D)** at every sufficiently large budget. Same-`k`
    prudence about a same-strength searcher is self-defeating; mutual defection is the
    honest fixed point. -/
theorem llm_outcome_CIMCIC_vs_PrudentBot :
    ∃ k₂, ∀ k, k₂ < k →
      ∃ fuel, outcome fuel (CIMCIC k) (PrudentBot k) = some (.D, .D) := by
  refine ⟨0, fun k _ => ⟨3, ?_⟩⟩
  have hA : play 3 (CIMCIC k) (PrudentBot k) = some .D :=
    CIMCIC_plays_D_against_PrudentBot k 1
  have hB : play 3 (PrudentBot k) (CIMCIC k) = some .D :=
    PrudentBot_plays_D_against_CIMCIC k 0
  exact outcome_of_plays _ _ _ _ _ hA hB

end PD.Theorems
