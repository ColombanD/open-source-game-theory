import PrisonersDilemma.Program
import PrisonersDilemma.Dynamics
import PrisonersDilemma.Bots.LlmGenerations.LegibleBot
import PrisonersDilemma.Bots.CupodTrollBot
import PrisonersDilemma.Theorems.CupodTrollBot.Helpers
import PrisonersDilemma.Base.Helpers
import PrisonersDilemma.BaseTheorems
import PrisonersDilemma.Theorems.LegibleBot.Helpers

open PD
open PD.BaseTheorems
open PD.Bots
namespace PD.Theorems

/-- LegibleBot vs CupodTrollBot, the whole FLOOR regime: the troll's identity
    guard fails at EVERY budget (a `.box`-guard searcher is not CupodBot), so
    it cooperates and is exploited by the floor-defector — `(D, C)`.
    The non-floor regime is RESOLVED (2026-07-30): see the staggered large-`k` theorem below. -/
theorem outcome_LegibleBot_vs_CupodTrollBot_floor (k fuel : Nat)
    (hszL : k < (Formula.box k
      (.plays (LegibleBot k k) (CupodTrollBot k) .C)).size) :
    outcome (fuel + 2) (LegibleBot k k) (CupodTrollBot k) = some (.D, .C) :=
  outcome_of_plays _ _ _ _ _ (LegibleBot_defects_floor k k fuel _ hszL)
    (CupodTrollBot_cooperates_if_opp_not_CupodBot k fuel (LegibleBot k k)
      (by simp [LegibleBot, CupodBot]))

/-- The concrete `k = 2` instance. -/
theorem outcome_LegibleBot_vs_CupodTrollBot_floor2 (fuel : Nat) :
    outcome (fuel + 2) (LegibleBot 2 2) (CupodTrollBot 2) = some (.D, .C) :=
  outcome_LegibleBot_vs_CupodTrollBot_floor 2 fuel (by decide)

/-- **LegibleBot (staggered) vs CupodTrollBot: `(C, C)`** for all sufficiently
    large `k` — at EVERY troll budget `j` (the family core's `B` absorbs the
    troll's `O(log j)` source size). The troll's `.eq` recognition guard is
    structurally false (LegibleBot is not literally `CupodBot j`), so it
    cooperates by default; LegibleBot's Löb cooperation is opponent-blind.
    Staggered complement of `outcome_LegibleBot_vs_CupodTrollBot_floor`. -/
theorem outcome_LegibleBot_vs_CupodTrollBot (j : Nat) :
    ∃ k₂, ∀ k, k > k₂ →
      ∃ fuel, outcome fuel (LegibleBot (2*k+64) k) (CupodTrollBot j) = some (.C, .C) := by
  obtain ⟨k₂, h⟩ := LegibleBot_cooperates_large (fun _ => CupodTrollBot j)
    ((CupodTrollBot j).size) (fun k => Nat.le_add_right _ _)
  refine ⟨k₂, fun k hk => ?_⟩
  obtain ⟨n, hn⟩ := h k hk
  have hn' : eval n (LegibleBot (2*k+64) k) (CupodTrollBot j) (LegibleBot (2*k+64) k)
      = some .C := hn
  have hL : play (n + 2) (LegibleBot (2*k+64) k) (CupodTrollBot j) = some .C :=
    eval_mono_le hn' _ (Nat.le_add_right _ 2)
  have hT : play (n + 2) (CupodTrollBot j) (LegibleBot (2*k+64) k) = some .C :=
    CupodTrollBot_cooperates_if_opp_not_CupodBot j n (LegibleBot (2*k+64) k)
      (by simp [LegibleBot, CupodBot])
  exact ⟨n + 2, outcome_of_plays _ _ _ _ _ hL hT⟩

end PD.Theorems
