import PrisonersDilemma.Bots.LlmGenerations.CIMCIC
import PrisonersDilemma.Bots.CupodBot
import PrisonersDilemma.Base.Helpers
import PrisonersDilemma.BaseTheorems
import PrisonersDilemma.Theorems.CupodBot.Helpers

/-!
# CIMCIC vs CupodBot — `(D, C)` at EVERY same budget, by the floor alone

The enlarged-zoo table stipulated this cell `(C, C)`; the tau layer's entangled
closure (2026-08-21, `cimcic_cupod_plays_D`/`cupod_cimcic_plays_C`) proved the
lifted pair `(D, C)` and thereby FALSIFIED the stipulation's value. This file is
the base-shape transplant:

* CIMCIC's guard is the implication "I cooperate with Cupod → Cupod cooperates
  with me". Its consequent is TRUE — CupodBot does trust CIMCIC — but that trust
  is CupodBot's ELSE-play, floor-priced (`no_provable_CupodBot_C_tail`), so
  `weakenImpl` has nothing to cite and the spine-tail census walks through the
  `.impl` to the floored consequent: the guard is unprovable and CIMCIC DEFECTS.
* CupodBot asks "does CIMCIC provably defect against me?" — it does, but the
  defection is CIMCIC's else-play, floored (`cb_no_provable_cimcic_D_tail`
  below) — CupodBot cannot convict and TRUSTS.

The `(C, C)` fixpoint is semantically consistent but PROVABILITY-inconsistent:
even in that world CupodBot's C stays an else-play, so CIMCIC's search can never
succeed. The floor forbids the self-fulfilling branch — no Löb gate, no
threshold, every `k`.
-/

open PD
open PD.BaseTheorems
open PD.Bots
namespace PD.Theorems

/-- No proof of ≤ k characters tails at "CIMCIC plays D against O" — its D is its
    else-slot (the mirror of `cd_no_provable_beta`, generic in the opponent). -/
theorem cb_no_provable_cimcic_D_tail (k : Nat) (O : Prog) :
    ∀ K φ, Pf K φ → K ≤ k →
      TailTo (.plays (CIMCIC k) O Action.D) φ → False := by
  intro K φ hp hK ht
  refine no_provable_tailToS_floor k (· = .plays (CIMCIC k) O Action.D)
    ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ K φ hp hK ((TailToS_singleton _ φ).2 ht)
  · rintro φ' rfl; exact ⟨_, _, _, rfl⟩
  · rintro K' hK' φ' rfl hA
    cases hA with
    | mk hpp hn =>
      unfold CIMCIC at hpp
      cases hpp with
      | search_t hg hbr => cases hbr
      | search_f hneg hbr => simp only [c_node] at hn; omega
  · rintro me oppo c hS g ψ b hme
    injection hS with h1 h2 h3; subst h1; subst h3
    unfold CIMCIC at hme; simp only [Prog.search.injEq] at hme
    exact absurd hme.2.2.1 (by simp)
  · rintro me oppo c hS p q hme
    injection hS with h1 h2 h3; subst h1; simp [CIMCIC] at hme
  · rintro me oppo c hS p q hme
    injection hS with h1 h2 h3; subst h1; simp [CIMCIC] at hme
  · rintro me oppo c hS g ψ b hme
    injection hS with h1 h2 h3; subst h1; simp [CIMCIC] at hme
  · rintro z a' g ψ c0 c1 q oppo hS
    injection hS with h1 h2 h3; simp [CIMCIC] at h1
  · rintro me oppo c hS k₁ ψ₁ k₂ ψ₂ c1 q hme
    injection hS with h1 h2 h3; subst h1; subst h3
    unfold CIMCIC at hme; simp only [Prog.search.injEq] at hme
    exact absurd hme.2.2.1 (by simp)
  · rintro me oppo c hS L hme
    injection hS with h1 h2 h3; subst h1; subst h3
    cases L with
    | nil => simp [searchPlug, CIMCIC] at hme
    | cons hd tl =>
        obtain ⟨g, ψ, e⟩ := hd
        simp only [searchPlug, CIMCIC, Prog.search.injEq] at hme
        have hcontra := hme.2.2.1
        rw [searchPlug_eq_ctxPlug tl (.const .D)] at hcontra
        exact const_ne_ctxPlug (by decide) _ hcontra
  · rintro me oppo c hS hd L hme
    injection hS with h1 h2 h3; subst h1; subst h3
    exfalso
    cases hd with
    | searchL g ψ e =>
        simp only [ctxPlug, CIMCIC, Prog.search.injEq] at hme
        have hcontra := hme.2.2.1
        exact const_ne_ctxPlug (by decide) L hcontra
    | iteL z aT other => simp [ctxPlug, CIMCIC] at hme
  · rintro me oppo c hS hd L hme
    injection hS with h1 h2 h3; subst h1; subst h3
    cases hd with
    | thenL g ψ e =>
        simp only [plug2, CIMCIC, Prog.search.injEq] at hme
        obtain ⟨-, -, hplug, -⟩ := hme
        exfalso
        cases L with
        | nil => simp [plug2] at hplug
        | cons hd2 tl2 => cases hd2 <;> simp [plug2] at hplug
    | elseL g P' Q' c' q =>
        simp only [plug2, CIMCIC, Prog.search.injEq] at hme
        exact absurd hme.2.1 (by simp)
  · rintro me oppo c hS defs i _ _ _ hme _
    injection hS with h1 h2 h3
    subst h1
    simp [CIMCIC] at hme
  · -- hbotsyssim: the `.sys` RUN twin, same shape kill
    rintro me oppo c hS defs i _ hme _
    injection hS with h1 h2 h3
    subst h1
    simp [CIMCIC] at hme

/-- CIMCIC's implication guard against CupodBot is unprovable at budget k: its
    spine tail is CupodBot's floored trust. -/
theorem cb_cimcic_guard_not_provable (k : Nat) :
    ¬ Pf k (.impl (.plays (CIMCIC k) (CupodBot k) Action.C)
                  (.plays (CupodBot k) (CIMCIC k) Action.C)) := by
  intro h
  refine no_provable_CupodBot_C_tail k (CIMCIC k) k _ h (Nat.le_refl k) ⟨rfl, ?_⟩
  intro hA
  simp only [TailTo] at hA
  exact absurd hA (by simp [CIMCIC, CupodBot])

theorem cb_proofSearch_false_cimcic (k : Nat) :
    proofSearch k
      ((Formula.impl (.plays .self .opp Action.C) (.plays .opp .self Action.C)).subst
        (CIMCIC k) (CupodBot k)) = false := by
  show proofSearch k
      (.impl (.plays (CIMCIC k) (CupodBot k) Action.C)
             (.plays (CupodBot k) (CIMCIC k) Action.C)) = false
  cases hps : proofSearch k
      (.impl (.plays (CIMCIC k) (CupodBot k) Action.C)
             (.plays (CupodBot k) (CIMCIC k) Action.C)) with
  | false => rfl
  | true => exact absurd ((proofSearch_spec k _).1 hps) (cb_cimcic_guard_not_provable k)

theorem cb_CIMCIC_plays_D (k fuel : Nat) :
    play (fuel + 2) (CIMCIC k) (CupodBot k) = some .D := by
  have hg := cb_proofSearch_false_cimcic k
  show (if proofSearch k
            ((Formula.impl (.plays .self .opp Action.C) (.plays .opp .self Action.C)).subst
              (CIMCIC k) (CupodBot k))
          then eval (fuel + 1) (CIMCIC k) (CupodBot k) (.const Action.C)
          else eval (fuel + 1) (CIMCIC k) (CupodBot k) (.const Action.D)) = some .D
  rw [hg]; simp [eval]

/-- CupodBot's guard against CIMCIC is FALSE at budget k: CIMCIC's defection is
    its own else-play — floored. -/
theorem cb_cupod_guard_false (k : Nat) :
    proofSearch k
      ((Formula.plays .opp .self Action.D).subst (CupodBot k) (CIMCIC k)) = false := by
  show proofSearch k (.plays (CIMCIC k) (CupodBot k) Action.D) = false
  cases h : proofSearch k (.plays (CIMCIC k) (CupodBot k) Action.D) with
  | false => rfl
  | true =>
      exact absurd rfl
        (fun hT => False.elim
          (cb_no_provable_cimcic_D_tail k (CupodBot k) k _
            ((proofSearch_spec _ _).1 h) (Nat.le_refl k) hT))

theorem cb_CupodBot_plays_C (k fuel : Nat) :
    play (fuel + 2) (CupodBot k) (CIMCIC k) = some .C := by
  have hg := cb_cupod_guard_false k
  show (if proofSearch k
            ((Formula.plays .opp .self Action.D).subst (CupodBot k) (CIMCIC k))
          then eval (fuel + 1) (CupodBot k) (CIMCIC k) (.const Action.D)
          else eval (fuel + 1) (CupodBot k) (CIMCIC k) (.const Action.C)) = some .C
  rw [hg]; simp [eval]

/-- **CIMCIC vs CupodBot → (D, C)**, at every budget and fuel ≥ 2 — the red-cell
    shape, one tier up: trust extended exactly where it cannot be verified. -/
theorem outcome_CIMCIC_vs_CupodBot (k fuel : Nat) :
    outcome (fuel + 2) (CIMCIC k) (CupodBot k) = some (.D, .C) :=
  outcome_of_plays _ _ _ _ _ (cb_CIMCIC_plays_D k fuel) (cb_CupodBot_plays_C k fuel)

end PD.Theorems
