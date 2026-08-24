import PrisonersDilemma.Bots.LlmGenerations.DIMCID
import PrisonersDilemma.Bots.DupocBot
import PrisonersDilemma.Base.Helpers
import PrisonersDilemma.BaseTheorems
import PrisonersDilemma.Theorems.DIMCID.Helpers
import PrisonersDilemma.Theorems.DupocBot.Helpers

/-!
# DIMCID vs DupocBot — `(C, D)` at EVERY same budget, by the floor alone

**This FALSIFIES the enlarged-zoo stipulation `(D, D)`.** The value was predicted
by the tau layer's alignment rule and its `dimcid × dupoc` closure
(`Tau/Theorems/TauDIMCID/Helpers`, `dimcid_dupoc_plays_C`), then transplanted
here — the second stipulation this method has overturned (after
`outcome_CIMCIC_vs_CupodBot`).

The pair is **ANTI-ALIGNED**: each bot's guard asks for an action the other's
THEN-branch does not produce.

* DIMCID's consequent asks DupocBot to play `D` — but `D` is DupocBot's
  ELSE-play, floor-priced (`no_provable_DupocBot_D_tail`). `search_t` cannot
  conclude it (then-action is `C`), and every other route pays the failed
  budget. So DIMCID's guard is unprovable and it takes its default: **C**.
* DupocBot's guard asks DIMCID to play `C` — but `C` is DIMCID's ELSE-play,
  floor-priced the same way (`no_provable_DIMCID_C_tail`). So DupocBot's guard
  is unprovable and it takes its default: **D**.

Two true facts, neither citable — the same shape as `outcome_JustBot_vs_CupodBot`.
No Löb gate: the floors are structural, so this holds at every `k`.

Contrast `DIMCID × CupodBot` (`vs_CupodBot.lean`), which is ALIGNED and closes
the other way, on mutual defection.
-/

open PD
open PD.BaseTheorems
open PD.Bots
namespace PD.Theorems

/-- DIMCID's guard against DupocBot is FALSE at budget k: its consequent asks
    for DupocBot's floor-priced else-play. -/
theorem dd_dimcid_guard_false (k : Nat) :
    proofSearch k
      ((Formula.impl (.plays .self .opp Action.C) (.plays .opp .self Action.D)).subst
        (DIMCID k) (DupocBot k)) = false := by
  show proofSearch k
      (.impl (.plays (DIMCID k) (DupocBot k) Action.C)
             (.plays (DupocBot k) (DIMCID k) Action.D)) = false
  cases h : proofSearch k
      (.impl (.plays (DIMCID k) (DupocBot k) Action.C)
             (.plays (DupocBot k) (DIMCID k) Action.D)) with
  | false => rfl
  | true =>
      exfalso
      refine no_provable_DupocBot_D_tail k (DIMCID k) k _
        ((proofSearch_spec _ _).1 h) (Nat.le_refl k) ⟨rfl, ?_⟩
      intro hA
      simp only [TailTo] at hA
      exact absurd hA (by simp [DIMCID, DupocBot])

theorem dd_DIMCID_plays_C (k fuel : Nat) :
    play (fuel + 2) (DIMCID k) (DupocBot k) = some .C := by
  have hg := dd_dimcid_guard_false k
  show (if proofSearch k
            ((Formula.impl (.plays .self .opp Action.C) (.plays .opp .self Action.D)).subst
              (DIMCID k) (DupocBot k))
          then eval (fuel + 1) (DIMCID k) (DupocBot k) (.const Action.D)
          else eval (fuel + 1) (DIMCID k) (DupocBot k) (.const Action.C)) = some .C
  rw [hg]; simp [eval]

/-- DupocBot's guard against DIMCID is FALSE at budget k: DIMCID's cooperation is
    its own else-play — floored. -/
theorem dd_dupoc_guard_false (k : Nat) :
    proofSearch k
      ((Formula.plays .opp .self Action.C).subst (DupocBot k) (DIMCID k)) = false := by
  show proofSearch k (.plays (DIMCID k) (DupocBot k) Action.C) = false
  cases h : proofSearch k (.plays (DIMCID k) (DupocBot k) Action.C) with
  | false => rfl
  | true =>
      exfalso
      exact no_provable_DIMCID_C_tail k (DupocBot k) k _
        ((proofSearch_spec _ _).1 h) (Nat.le_refl k) rfl

theorem dd_DupocBot_plays_D (k fuel : Nat) :
    play (fuel + 2) (DupocBot k) (DIMCID k) = some .D := by
  have hg := dd_dupoc_guard_false k
  show (if proofSearch k
            ((Formula.plays .opp .self Action.C).subst (DupocBot k) (DIMCID k))
          then eval (fuel + 1) (DupocBot k) (DIMCID k) (.const Action.C)
          else eval (fuel + 1) (DupocBot k) (DIMCID k) (.const Action.D)) = some .D
  rw [hg]; simp [eval]

/-- **DIMCID vs DupocBot → (C, D)**, at every budget and fuel ≥ 2. -/
theorem outcome_DIMCID_vs_DupocBot (k fuel : Nat) :
    outcome (fuel + 2) (DIMCID k) (DupocBot k) = some (.C, .D) :=
  outcome_of_plays _ _ _ _ _ (dd_DIMCID_plays_C k fuel) (dd_DupocBot_plays_D k fuel)

end PD.Theorems
