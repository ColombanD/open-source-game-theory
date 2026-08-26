import PrisonersDilemma.Bots.CupodTrollBot
import PrisonersDilemma.Bots.CupodBot


import PrisonersDilemma.Dynamics
import PrisonersDilemma.BaseTheorems
import PrisonersDilemma.Base.Helpers
import PrisonersDilemma.Theorems.CupodTrollBot.Helpers
import PrisonersDilemma.Outcome

open PD
open PD.Bots
open PD.BaseTheorems
namespace PD.Theorems
/-- CupodTrollBot vs CupodBot: the troll recognises CupodBot by its literal source and
    defects; CupodBot's guard (`□(opp plays D vs me)`) is certified by `search_t` over
    the `eqRefl` leaf, so it defects too. The only condition is a budget FLOOR — `k`
    must cover the `.eq` formula's size, which is logarithmic in `k` — so the honest
    regime is `.eventual`, with no side condition and no dagger. (Until 2026-08-26 this
    was stated with an `OutcomeSpecIf` guard `size ≤ k ∧ atom_cost (fuel + 2) ≤ k`; the
    second conjunct was never used by the proof.) -/
@[outcome]
theorem outcome_CupodTrollBot_vs_CupodBot :
    OutcomeSpec .eventual 2 CupodTrollBot CupodBot (some (.D, .D)) := by
  -- The floor: `(Formula.eq (CupodBot k) (CupodBot k)).size` is `A·log2 k + B`.
  have hsz : ∀ k, (Formula.eq (CupodBot k) (CupodBot k)).size ≤ 100 * Nat.log2 k + 1000 := by
    intro k
    simp only [numCost, Formula.size, Prog.size, CupodBot]
    omega
  obtain ⟨K, hK⟩ := linear_log2_add_le 100 1000
  refine ⟨K, fun k hk fuel => ?_⟩
  have hk' : (Formula.eq (CupodBot k) (CupodBot k)).size ≤ k :=
    le_trans (hsz k) (hK k (by omega))
  have hA : play (fuel + 2) (CupodTrollBot k) (CupodBot k) = some .D :=
    CupodTrollBot_defects_vs_CupodBot k fuel hk'
  have hB : play (fuel + 2) (CupodBot k) (CupodTrollBot k) = some .D :=
    CupodBot_defects_vs_CupodTrollBot k fuel hk'
  exact outcome_of_plays _ _ _ _ _ hA hB

end PD.Theorems
