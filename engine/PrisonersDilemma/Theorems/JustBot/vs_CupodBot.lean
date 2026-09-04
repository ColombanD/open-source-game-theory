import PrisonersDilemma.Bots.LlmGenerations.JustBot
import PrisonersDilemma.Bots.CupodBot
import PrisonersDilemma.Bots.DupocBot
import PrisonersDilemma.Base.Helpers
import PrisonersDilemma.BaseTheorems
import PrisonersDilemma.Theorems.JustBot.Helpers
import PrisonersDilemma.Theorems.CupodBot.Helpers
import PrisonersDilemma.Outcome

/-!
# JustBot vs CupodBot — `(D, C)` at EVERY same budget, by the floor alone

The former frontier stipulation, now a theorem — PREDICTED by the tau layer's
entangled closure (2026-08-21): the (τ(Just), τ(Cupod)) cell closed as `(D, C)`
by `ps_botSys_mismatch_false`, and the argument transfers to the base shapes.

* JustBot asks "does my opponent provably cooperate with DupocBot?" — CupodBot
  DOES trust DupocBot (the red cell), but that trust is its ELSE-play, floor-priced
  (`no_provable_CupodBot_C_tail`) — so JustBot cannot cite it and DEFECTS.
* CupodBot asks "does my opponent provably defect against me?" — JustBot DOES
  defect, but that defection is ITS else-play, floor-priced
  (`no_provable_JustBot_D_tail`) — so CupodBot cannot convict and TRUSTS.

Two true facts, neither citable: the norm-enforcer punishes what it cannot verify,
the suspicious cooperator extends the trust it cannot refute. No Löb gate, no
threshold — the floors are structural, so the outcome holds at every `k`.
-/

open PD
open PD.BaseTheorems
open PD.Bots
namespace PD.Theorems

/-- JustBot's guard against CupodBot does not fire at budget k (`¬ ⊢_k`; the formula
    itself is `⊨`-true): "CupodBot plays C vs frozen DupocBot" is true only through
    CupodBot's floor. -/
theorem jc_just_guard_false (k : Nat) :
    proofSearch k
      ((Formula.plays .opp (.bot (DupocBot k)) Action.C).subst
        (JustBot k) (CupodBot k)) = false := by
  show proofSearch k (.plays (CupodBot k) (.bot (DupocBot k)) Action.C) = false
  cases h : proofSearch k (.plays (CupodBot k) (.bot (DupocBot k)) Action.C) with
  | false => rfl
  | true =>
      exact absurd rfl
        (fun hT => False.elim
          (no_provable_CupodBot_C_tail k (.bot (DupocBot k)) k _
            ((proofSearch_spec _ _).1 h) (Nat.le_refl k) hT))

theorem jc_JustBot_plays_D (k fuel : Nat) :
    play (fuel + 2) (JustBot k) (CupodBot k) = some .D := by
  have hg := jc_just_guard_false k
  show (if proofSearch k
            ((Formula.plays .opp (.bot (DupocBot k)) Action.C).subst
              (JustBot k) (CupodBot k))
          then eval (fuel + 1) (JustBot k) (CupodBot k) (.const Action.C)
          else eval (fuel + 1) (JustBot k) (CupodBot k) (.const Action.D)) = some .D
  rw [hg]; simp [eval]

/-- CupodBot's guard against JustBot does not fire at budget k (`¬ ⊢_k`, the defection
    is real): JustBot's defection is its own else-play — floored. -/
theorem jc_cupod_guard_false (k : Nat) :
    proofSearch k
      ((Formula.plays .opp .self Action.D).subst (CupodBot k) (JustBot k)) = false := by
  show proofSearch k (.plays (JustBot k) (CupodBot k) Action.D) = false
  cases h : proofSearch k (.plays (JustBot k) (CupodBot k) Action.D) with
  | false => rfl
  | true =>
      exact absurd rfl
        (fun hT => False.elim
          (no_provable_JustBot_D_tail k (CupodBot k) k _
            ((proofSearch_spec _ _).1 h) (Nat.le_refl k) hT))

theorem jc_CupodBot_plays_C (k fuel : Nat) :
    play (fuel + 2) (CupodBot k) (JustBot k) = some .C := by
  have hg := jc_cupod_guard_false k
  show (if proofSearch k
            ((Formula.plays .opp .self Action.D).subst (CupodBot k) (JustBot k))
          then eval (fuel + 1) (CupodBot k) (JustBot k) (.const Action.D)
          else eval (fuel + 1) (CupodBot k) (JustBot k) (.const Action.C)) = some .C
  rw [hg]; simp [eval]

/-- **JustBot vs CupodBot → (D, C)**, at every budget and fuel ≥ 2. -/
@[outcome]
theorem outcome_JustBot_vs_CupodBot :
    OutcomeSpec .universal 2
      JustBot CupodBot (some (.D, .C)) :=
  fun k fuel =>
  outcome_of_plays _ _ _ _ _ (jc_JustBot_plays_D k fuel) (jc_CupodBot_plays_C k fuel)

end PD.Theorems
