import PrisonersDilemma.Program
import PrisonersDilemma.Dynamics
import PrisonersDilemma.BaseTheorems
import PrisonersDilemma.Base.Asymptotics
import PrisonersDilemma.Base.Helpers

import PrisonersDilemma.Bots.LlmGenerations.CIMCIC
import PrisonersDilemma.Bots.CooperateBot
import PrisonersDilemma.Theorems.CooperateBot.Helpers

open PD
open PD.BaseTheorems
open PD.Bots
namespace PD.Theorems

/-- The consequent of CIMCIC's guard against CooperateBot is provable at any large
    enough budget: CooperateBot cooperates with CIMCIC. -/
theorem CIMCIC_consequent_CooperateBot (k : Nat) :
    Pf (atom_cost 1) (Formula.plays CooperateBot (CIMCIC k) Action.C) :=
  Pf.atom ⟨PlaysProof.const, by decide⟩

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
  show Pf k
    (Formula.impl (.plays (CIMCIC k) CooperateBot Action.C)
                  (.plays CooperateBot (CIMCIC k) Action.C))
  refine Pf.weakenImpl _ _ (atom_cost 1) (CIMCIC_consequent_CooperateBot k) ?_
  -- transcript: consequent certificate (`atom_cost 1 = 3`) + the implication's size, ≤ k.
  have hb := hK k hk
  have h1 : atom_cost 1 = 3 := by decide
  simp only [numCost, Formula.size, Prog.size, CIMCIC, CooperateBot]
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
theorem outcome_CIMCIC_vs_CooperateBot :
    ∃ k, ∀ fuel, outcome (fuel + 2) (CIMCIC k) CooperateBot = some (.C, .C) := by
  obtain ⟨K, hK⟩ := proofSearch_true_for_CIMCIC_vs_CooperateBot
  refine ⟨K + 1, fun fuel => ?_⟩
  have hk := hK (K + 1) (Nat.le_succ K)
  have hA : play (fuel + 2) (CIMCIC (K + 1)) CooperateBot = some .C :=
    CIMCIC_plays_C_against_CooperateBot (K + 1) fuel hk
  have hB : play (fuel + 2) CooperateBot (CIMCIC (K + 1)) = some .C := by
    simpa [Nat.add_comm] using play_CooperateBot (fuel + 1) (CIMCIC (K + 1))
  exact outcome_of_plays _ _ _ _ _ hA hB

end PD.Theorems
