import PrisonersDilemma.Program
import PrisonersDilemma.Dynamics
import PrisonersDilemma.BaseTheorems
import PrisonersDilemma.Base.Asymptotics
import PrisonersDilemma.Base.Helpers

import PrisonersDilemma.Bots.LlmGenerations.CIMCIC

open PD
open PD.BaseTheorems
open PD.Bots
namespace PD.Theorems

/-!
# CIMCIC vs CIMCIC — self-play cooperation via `implRefl`

THE `identImpl` PROPOSAL, RESOLVED (2026-07-28). The proof agent filed the
`identImpl` constructor proposal (2026-07-27, `app/generated/constructor_proposals/`)
for exactly this matchup: CIMCIC's guard against a copy of itself substitutes to the
TAUTOLOGY `A → A` (`A = CIMCIC plays C vs CIMCIC`), which the pre-completion `S`
could not prove — the historical trigger of the Family-B completion program. The
proposal landed as `Pf.implRefl` (with `implK`/`implS` and the admissible deduction
theorem alongside), and the blocked outcome is now a THEOREM: past the `O(log k)`
size threshold the guard fires by reflexivity and both copies cooperate.

The theorem keeps the agent's `llm_outcome_` prefix: it is the LLM-proposed result,
integrated per the Tier-2 playbook. -/

/-- CIMCIC's guard against ITSELF is provable — it is the reflexive implication
    `A → A`, a one-line `Pf.implRefl` once the budget holds its `O(log k)` size. -/
theorem proofSearch_true_for_CIMCIC_vs_CIMCIC :
    ∃ K, ∀ k, k ≥ K →
      proofSearch k
        ((Formula.impl (.plays .self .opp Action.C) (.plays .opp .self Action.C)).subst
          (CIMCIC k) (CIMCIC k)) = true := by
  obtain ⟨K, hK⟩ := linear_log2_add_le 10 100
  refine ⟨K, fun k hk => ?_⟩
  refine (proofSearch_spec _ _).2 ?_
  show Pf k
    (Formula.impl (.plays (CIMCIC k) (CIMCIC k) Action.C)
                  (.plays (CIMCIC k) (CIMCIC k) Action.C))
  refine Pf.implRefl _ ?_
  have hb := hK k hk
  simp only [numCost, Formula.size, Prog.size, CIMCIC]
  omega

/-- CIMCIC cooperates against its copy: the reflexivity guard fires, so the search
    takes the `.const .C` branch. -/
theorem CIMCIC_plays_C_against_CIMCIC (k fuel : Nat)
    (hk : proofSearch k
        ((Formula.impl (.plays .self .opp Action.C) (.plays .opp .self Action.C)).subst
          (CIMCIC k) (CIMCIC k)) = true) :
    play (fuel + 2) (CIMCIC k) (CIMCIC k) = some .C := by
  show (if proofSearch k
            ((Formula.impl (.plays .self .opp Action.C) (.plays .opp .self Action.C)).subst
              (CIMCIC k) (CIMCIC k))
          then eval (fuel + 1) (CIMCIC k) (CIMCIC k) (.const Action.C)
          else eval (fuel + 1) (CIMCIC k) (CIMCIC k) (.const Action.D)) = some .C
  rw [hk]; simp [eval]

/-- **CIMCIC vs CIMCIC: mutual cooperation past the size threshold** — the
    `identImpl`-proposal outcome, unblocked by `Pf.implRefl`. -/
theorem llm_outcome_CIMCIC_vs_CIMCIC :
    ∃ k₂, ∀ k, k₂ < k → ∃ fuel,
      outcome fuel (CIMCIC k) (CIMCIC k) = some (.C, .C) := by
  obtain ⟨K, hK⟩ := proofSearch_true_for_CIMCIC_vs_CIMCIC
  refine ⟨K, fun k hk => ⟨2, ?_⟩⟩
  have hg := hK k (Nat.le_of_lt hk)
  have hA : play (0 + 2) (CIMCIC k) (CIMCIC k) = some .C :=
    CIMCIC_plays_C_against_CIMCIC k 0 hg
  exact outcome_of_plays _ _ _ _ _ hA hA

end PD.Theorems
