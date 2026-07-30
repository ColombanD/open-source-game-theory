import PrisonersDilemma.Program
import PrisonersDilemma.Dynamics
import PrisonersDilemma.Bots.LlmGenerations.LegibleBot
import PrisonersDilemma.Base.Helpers
import PrisonersDilemma.BaseTheorems
import PrisonersDilemma.Theorems.LegibleBot.Helpers

open PD
open PD.BaseTheorems
open PD.Bots
namespace PD.Theorems

/-- LegibleBot self-play, the whole FLOOR regime: neither copy can see its own
    legibility, so neither cooperates — the tragic dual of WaryBot's
    floor-trust. Large-`k` self-play is RESOLVED (2026-07-30): the two-box Löb fixpoint closes via `searchBranch`+`box4`+`pblt_engine`; see the staggered theorem below. -/
theorem outcome_LegibleBot_vs_LegibleBot_floor (kOut kIn fuel : Nat)
    (hsz : kOut < (Formula.box kIn
      (.plays (LegibleBot kOut kIn) (LegibleBot kOut kIn) .C)).size) :
    outcome (fuel + 2) (LegibleBot kOut kIn) (LegibleBot kOut kIn) = some (.D, .D) :=
  outcome_of_plays _ _ _ _ _ (LegibleBot_defects_floor kOut kIn fuel _ hsz)
    (LegibleBot_defects_floor kOut kIn fuel _ hsz)

/-- The concrete `(2, 2)` instance. -/
theorem outcome_LegibleBot_vs_LegibleBot_floor2 (fuel : Nat) :
    outcome (fuel + 2) (LegibleBot 2 2) (LegibleBot 2 2) = some (.D, .D) :=
  outcome_LegibleBot_vs_LegibleBot_floor 2 2 fuel (by decide)

/-- **LegibleBot (staggered) self-play: `(C, C)`** for all sufficiently large
    `k`. The doubly self-referential fixpoint resolves: unlike single-tier
    PrudentBot (whose same-`k` self-play is self-defeating), the `2k+64 / k`
    stagger gives the outer prover room to cite the inner box, and both copies
    are the SAME program — one core instantiation (family
    `X k := LegibleBot (2k+64) k`, size `O(log k)` within the `B + 20·log2 k`
    budget) supplies both plays. Staggered complement of
    `outcome_LegibleBot_vs_LegibleBot_floor`. -/
theorem outcome_LegibleBot_vs_LegibleBot :
    ∃ k₂, ∀ k, k > k₂ →
      ∃ fuel, outcome fuel (LegibleBot (2*k+64) k) (LegibleBot (2*k+64) k)
        = some (.C, .C) := by
  obtain ⟨k₂, h⟩ := LegibleBot_cooperates_large (fun k => LegibleBot (2*k+64) k) 100
    (fun k => by
      have hst := log2_stagger_le k
      simp only [LegibleBot, Prog.size, Formula.size, numCost]
      omega)
  refine ⟨k₂, fun k hk => ?_⟩
  obtain ⟨n, hn⟩ := h k hk
  exact ⟨n, outcome_of_plays _ _ _ _ _ hn hn⟩

end PD.Theorems
