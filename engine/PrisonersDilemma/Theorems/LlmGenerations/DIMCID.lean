import PrisonersDilemma.Program
import PrisonersDilemma.Dynamics
import PrisonersDilemma.Axioms
import PrisonersDilemma.Bots.CooperateBot
import PrisonersDilemma.Bots.DefectBot
import PrisonersDilemma.Bots.LlmGenerations.DIMCID
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
# DIMCID outcomes

DIMCID ("Defect If My Cooperation Implies Defection") is

  `.search k (.impl (.plays .self .opp .C) (.plays .opp .self .D)) (.const .D) (.const .C)`

i.e. its guard is the implication "if I cooperate against the opponent, the
opponent defects against me"; if that is provable it **defects**, otherwise it
cooperates. Against opponent `X` the guard substitutes to

  `.impl (.plays (DIMCID k) X .C) (.plays X (DIMCID k) .D)`.

This is the mirror image of CIMCIC, and like CIMCIC it is made provable by the
`Provable.weakenImpl` rule (see `Derivation.lean` and the CIMCIC theorem file):
the implication is provable whenever its consequent is.

## The two outcomes

* **vs DefectBot — (D, D), proved below.** The consequent `.plays DefectBot
  (DIMCID k) .D` is provable (DefectBot defects against everything), so the guard
  is provable via `weakenImpl`, DIMCID's search fires, and it defects.

* **vs CooperateBot — NOT provable, by design (incompleteness boundary).** The
  consequent `.plays CooperateBot (DIMCID k) .D` is *false* (CooperateBot never
  defects), so `weakenImpl` does not apply. The implication is semantically true
  vacuously, so making DIMCID *cooperate* (take the else-branch) would require
  certifying the guard *unprovable* — a Π₁ statement the sound rules cannot
  establish. Deliberately left unproved; see the bottom of the file (symmetric to
  CIMCIC vs DefectBot).
-/

-- DefectBot --

/-- The consequent of DIMCID's guard against DefectBot is provable: DefectBot
    defects against DIMCID. -/
theorem DIMCID_consequent_DefectBot (k : Nat) :
    Provable (atom_cost 1) (Formula.plays DefectBot (DIMCID k) Action.D) :=
  Provable.atom (atom_complete DefectBot (DIMCID k) .D 1
    (by simpa using play_DefectBot 0 (DIMCID k)))

/-- DIMCID's guard against DefectBot is provable: `weakenImpl` turns the provable
    consequent into the implication, once `k` is large enough for the
    implication's `O(log k)` character size. -/
theorem proofSearch_true_for_DIMCID_vs_DefectBot :
    ∃ K, ∀ k, k ≥ K →
      proofSearch k
        ((Formula.impl (.plays .self .opp Action.C) (.plays .opp .self Action.D)).subst
          (DIMCID k) DefectBot) = true := by
  obtain ⟨K, hK⟩ := linear_log2_add_le 10 100
  refine ⟨K, fun k hk => ?_⟩
  refine (proofSearch_spec _ _).2 ?_
  show Provable k
    (Formula.impl (.plays (DIMCID k) DefectBot Action.C)
                  (.plays DefectBot (DIMCID k) Action.D))
  refine Provable.weakenImpl _ _ (atom_cost 1) (DIMCID_consequent_DefectBot k) ?_
  have hb := hK k hk
  simp only [Formula.size, Prog.size, DIMCID, DefectBot]
  omega

/-- DIMCID defects against DefectBot: its guard fires (proved above), so it takes
    the `.const .D` branch. -/
theorem DIMCID_plays_D_against_DefectBot (k fuel : Nat)
    (hk : proofSearch k
        ((Formula.impl (.plays .self .opp Action.C) (.plays .opp .self Action.D)).subst
          (DIMCID k) DefectBot) = true) :
    play (fuel + 2) (DIMCID k) DefectBot = some .D := by
  show (if proofSearch k
            ((Formula.impl (.plays .self .opp Action.C) (.plays .opp .self Action.D)).subst
              (DIMCID k) DefectBot)
          then eval (fuel + 1) (DIMCID k) DefectBot (.const Action.D)
          else eval (fuel + 1) (DIMCID k) DefectBot (.const Action.C)) = some .D
  rw [hk]; simp [eval]

/-- DIMCID vs DefectBot: mutual defection. -/
theorem DIMCID_vs_DefectBot :
    ∃ k, ∀ fuel, outcome (fuel + 2) (DIMCID k) DefectBot = some (.D, .D) := by
  obtain ⟨K, hK⟩ := proofSearch_true_for_DIMCID_vs_DefectBot
  refine ⟨K + 1, fun fuel => ?_⟩
  have hk := hK (K + 1) (Nat.le_succ K)
  have hA : play (fuel + 2) (DIMCID (K + 1)) DefectBot = some .D :=
    DIMCID_plays_D_against_DefectBot (K + 1) fuel hk
  have hB : play (fuel + 2) DefectBot (DIMCID (K + 1)) = some .D := by
    simpa [Nat.add_comm] using play_DefectBot (fuel + 1) (DIMCID (K + 1))
  exact outcome_of_plays _ _ _ _ _ hA hB

/-
## DIMCID vs CooperateBot — left unproved (incompleteness boundary)

Symmetric to CIMCIC vs DefectBot. The intended outcome is (C, C): DIMCID's guard
fails, so it falls through to `.const .C`. But "the guard search returns false" is
the Π₁ claim that the (semantically true, vacuously-satisfied) implication

  `.plays (DIMCID k) CooperateBot .C → .plays CooperateBot (DIMCID k) .D`

has no proof of size ≤ k — unprovability of a *true* formula, which the sound rules
cannot certify. Deliberately omitted rather than stated with `sorry`.
-/

end PD.Theorems
