import PrisonersDilemma.Program
import PrisonersDilemma.Dynamics
import PrisonersDilemma.Bots.LlmGenerations.LegibleBot
import PrisonersDilemma.Bots.LlmGenerations.DIMCID
import PrisonersDilemma.Base.Helpers
import PrisonersDilemma.BaseTheorems
import PrisonersDilemma.Theorems.LegibleBot.Helpers

open PD
open PD.BaseTheorems
open PD.Bots
namespace PD.Theorems

/-- LegibleBot vs DIMCID, the whole FLOOR regime: the floor-defector exploits
    the floor-trusting DIMCID — `(D, C)`. Large-`k` is RESOLVED (2026-07-30)
    at staggered dials: see the theorem below. -/
theorem outcome_LegibleBot_vs_DIMCID_floor (k fuel : Nat)
    (hszL : k < (Formula.box k
      (.plays (LegibleBot k k) (DIMCID k) .C)).size)
    (hszI : k < (Formula.impl (.plays (DIMCID k) (LegibleBot k k) .C)
      (.plays (LegibleBot k k) (DIMCID k) .D)).size) :
    outcome (fuel + 2) (LegibleBot k k) (DIMCID k) = some (.D, .C) :=
  outcome_of_plays _ _ _ _ _ (LegibleBot_defects_floor k k fuel _ hszL)
    (DIMCID_plays_C_against_LegibleBot_floor k fuel hszI)

/-- The concrete `k = 2` instance. -/
theorem outcome_LegibleBot_vs_DIMCID_floor2 (fuel : Nat) :
    outcome (fuel + 2) (LegibleBot 2 2) (DIMCID 2) = some (.D, .C) :=
  outcome_LegibleBot_vs_DIMCID_floor 2 fuel (by decide) (by decide)

/-- **LegibleBot (staggered) vs DIMCID (same inner dial `k`): `(C, C)`** for all
    sufficiently large `k`. DIMCID's malicious guard `(DIMCID plays C) → (L
    plays D)` is tailed at L's ELSE-play: the action-refined census
    (`ld_no_provable_tail` — the set kernel, since LegibleBot is a both-const
    searcher) shows no ≤`k` proof reaches it, so DIMCID's search fails and it
    falls through to cooperation (every `k`); LegibleBot's Löb cooperation is
    opponent-blind. Staggered complement of
    `outcome_LegibleBot_vs_DIMCID_floor`. -/
theorem outcome_LegibleBot_vs_DIMCID :
    ∃ k₂, ∀ k, k > k₂ →
      ∃ fuel, outcome fuel (LegibleBot (2*k+64) k) (DIMCID k) = some (.C, .C) := by
  obtain ⟨k₂, h⟩ := LegibleBot_cooperates_large (fun k => DIMCID k) 100
    (fun k => by simp only [DIMCID, Prog.size, Formula.size, numCost]; omega)
  refine ⟨k₂, fun k hk => ?_⟩
  obtain ⟨n, hn⟩ := h k hk
  have hn' : eval n (LegibleBot (2*k+64) k) (DIMCID k) (LegibleBot (2*k+64) k)
      = some .C := hn
  have hL : play (n + 2) (LegibleBot (2*k+64) k) (DIMCID k) = some .C :=
    eval_mono_le hn' _ (Nat.le_add_right _ 2)
  have hD : play (n + 2) (DIMCID k) (LegibleBot (2*k+64) k) = some .C :=
    DIMCID_plays_C_against_LegibleBot k n
  exact ⟨n + 2, outcome_of_plays _ _ _ _ _ hL hD⟩

end PD.Theorems
