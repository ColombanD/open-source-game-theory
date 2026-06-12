import PrisonersDilemma.Program
import PrisonersDilemma.Dynamics
import PrisonersDilemma.Axioms
import PrisonersDilemma.Bots.CooperateBot
import PrisonersDilemma.Bots.DefectBot
import PrisonersDilemma.Bots.LlmGenerations.CIMCIC
import PrisonersDilemma.Theorems.CooperateBot
import PrisonersDilemma.Theorems.DefectBot
import PrisonersDilemma.Theorems.Helpers
import PrisonersDilemma.BaseTheorems
import PrisonersDilemma.SizeLemmas

open PD
open PD.Axioms
open PD.BaseTheorems
open PD.Bots
namespace PD.Theorems

/-!
# CIMCIC outcomes

CIMCIC ("Cooperate If My Cooperation Implies Cooperation") is

  `.search k (.impl (.plays .self .opp .C) (.plays .opp .self .C)) (.const .C) (.const .D)`

i.e. its guard is the **implication** "if I cooperate against the opponent, the
opponent cooperates against me". Against opponent `X` the guard substitutes to

  `.impl (.plays (CIMCIC k) X .C) (.plays X (CIMCIC k) .C)`.

## What made this provable: the `weakenImpl` rule

Proving an *implication* guard requires building a proof of `.impl A B` at the
`Provable` level. The original proof system had no way to introduce an implication
from a true consequent — `Derivation` only had `modusPonens`, `hypSyll`,
`searchBranch`, `simStep`, `eqRefl`, none of which produces `.impl A B` from a
proof of `B`. (This is precisely why the earlier automated attempt at CIMCIC
failed.)

We added the sound, faithful rule `Provable.weakenImpl` (in `Derivation.lean`):
from `Provable m ψ` conclude `Provable k (.impl φ ψ)` whenever the conclusion's
character size fits `k`. It is sound because `interp (.impl φ ψ) = φ.interp →
ψ.interp`, which follows from `ψ.interp` by `fun _ => ·`; it is faithful because a
PA-like `S` always proves `ψ ⊢ φ → ψ`.

## The two outcomes

* **vs CooperateBot — (C, C), proved below.** The consequent `.plays CooperateBot
  (CIMCIC k) .C` is provable (CooperateBot cooperates with everything), so the
  guard is provable via `weakenImpl`, CIMCIC's search fires, and it cooperates.

* **vs DefectBot — NOT provable, by design (incompleteness boundary).** Here the
  consequent `.plays DefectBot (CIMCIC k) .C` is *false* (DefectBot never plays C),
  so `weakenImpl` does not apply. The implication is nonetheless *semantically
  true* — its antecedent `.plays (CIMCIC k) DefectBot .C` is false (CIMCIC defects
  against DefectBot), so it holds vacuously. To make CIMCIC *defect* against
  DefectBot we would need `proofSearch k guard = false`, i.e. to certify that this
  true-but-vacuous implication is **unprovable** within budget `k`. That is a Π₁
  statement about the oracle's incompleteness, which the sound rules cannot
  establish (the `= false` direction is discharged by refuting `guard.interp`, but
  here `guard.interp` is *true*). So CIMCIC vs DefectBot sits on the genuine
  incompleteness boundary and is deliberately left unproved. See the note at the
  bottom of the file.
-/

-- CooperateBot --

/-- The consequent of CIMCIC's guard against CooperateBot is provable at any large
    enough budget: CooperateBot cooperates with CIMCIC. -/
theorem CIMCIC_consequent_CooperateBot (k : Nat) :
    Provable (atom_cost 1) (Formula.plays CooperateBot (CIMCIC k) Action.C) :=
  Provable.atom (atom_complete CooperateBot (CIMCIC k) .C 1
    (by simpa using play_CooperateBot 0 (CIMCIC k)))

/-- CIMCIC's guard against CooperateBot is provable: the `weakenImpl` rule turns
    the provable consequent into the implication, once the budget `k` is large
    enough to hold the implication's character size (`O(log k)`, by
    `linear_log2_add_le`). -/
theorem proofSearch_true_for_CIMCIC_vs_CooperateBot :
    ∃ K, ∀ k, k ≥ K →
      proofSearch k
        ((Formula.impl (.plays .self .opp Action.C) (.plays .opp .self Action.C)).subst
          (CIMCIC k) CooperateBot) = true := by
  -- The substituted guard is `.impl (.plays (CIMCIC k) CooperateBot .C)
  --                                  (.plays CooperateBot (CIMCIC k) .C)`.
  -- Its size is `5 * log2 k + C` for a constant `C` (CIMCIC k costs `log2 k + …`),
  -- so `linear_log2_add_le` gives a `K` past which it fits within budget `k`.
  -- We pick a generous linear bound and discharge the exact size goal with `omega`.
  obtain ⟨K, hK⟩ := linear_log2_add_le 10 100
  refine ⟨K, fun k hk => ?_⟩
  refine (proofSearch_spec _ _).2 ?_
  show Provable k
    (Formula.impl (.plays (CIMCIC k) CooperateBot Action.C)
                  (.plays CooperateBot (CIMCIC k) Action.C))
  refine Provable.weakenImpl _ _ (atom_cost 1) (CIMCIC_consequent_CooperateBot k) ?_
  -- size of the implication fits within `k`.
  have hb := hK k hk
  simp only [Formula.size, Prog.size, CIMCIC, CooperateBot]
  omega

/-- CIMCIC cooperates against CooperateBot: its guard fires (proved above), so it
    takes the `.const .C` branch. -/
theorem CIMCIC_plays_C_against_CooperateBot (k fuel : Nat)
    (hk : proofSearch k
        ((Formula.impl (.plays .self .opp Action.C) (.plays .opp .self Action.C)).subst
          (CIMCIC k) CooperateBot) = true) :
    play (fuel + 2) (CIMCIC k) CooperateBot = some .C := by
  -- One eval step: the guard `proofSearch` argument is definitionally the
  -- substituted implication that `hk` proves true, so the search takes the
  -- `.const .C` branch.
  show (if proofSearch k
            ((Formula.impl (.plays .self .opp Action.C) (.plays .opp .self Action.C)).subst
              (CIMCIC k) CooperateBot)
          then eval (fuel + 1) (CIMCIC k) CooperateBot (.const Action.C)
          else eval (fuel + 1) (CIMCIC k) CooperateBot (.const Action.D)) = some .C
  rw [hk]; simp [eval]

/-- CIMCIC vs CooperateBot: mutual cooperation. -/
theorem CIMCIC_vs_CooperateBot :
    ∃ k, ∀ fuel, outcome (fuel + 2) (CIMCIC k) CooperateBot = some (.C, .C) := by
  obtain ⟨K, hK⟩ := proofSearch_true_for_CIMCIC_vs_CooperateBot
  refine ⟨K + 1, fun fuel => ?_⟩
  have hk := hK (K + 1) (Nat.le_succ K)
  have hA : play (fuel + 2) (CIMCIC (K + 1)) CooperateBot = some .C :=
    CIMCIC_plays_C_against_CooperateBot (K + 1) fuel hk
  have hB : play (fuel + 2) CooperateBot (CIMCIC (K + 1)) = some .C := by
    simpa [Nat.add_comm] using play_CooperateBot (fuel + 1) (CIMCIC (K + 1))
  exact outcome_of_plays _ _ _ _ _ hA hB

/-
## CIMCIC vs DefectBot — left unproved (incompleteness boundary)

The intended outcome is (D, D): CIMCIC's guard cannot be discharged, so it falls
through to `.const .D`. But "the guard search returns false" is the Π₁ claim that
the (semantically true, vacuously-satisfied) implication

  `.plays (CIMCIC k) DefectBot .C → .plays DefectBot (CIMCIC k) .C`

has no proof of size ≤ k. Our sound proof system cannot certify unprovability of a
*true* formula, and the `= false` discharge route (`proofSearch_sound` +
`¬ interp`) is unavailable because the implication's `interp` is true. Closing this
would require either an oracle-completeness axiom restricted to the decidable
fragment, or a metatheoretic argument outside `S`. It is therefore deliberately
omitted rather than stated with `sorry`.
-/

end PD.Theorems
