import PrisonersDilemma.Program
import PrisonersDilemma.Dynamics
import PrisonersDilemma.Bots.LlmGenerations.LegibleBot
import PrisonersDilemma.Bots.CooperateBot
import PrisonersDilemma.Theorems.CooperateBot.Helpers
import PrisonersDilemma.Base.Helpers
import PrisonersDilemma.BaseTheorems
import PrisonersDilemma.Theorems.LegibleBot.Helpers

open PD
open PD.BaseTheorems
open PD.Bots
namespace PD.Theorems

/-- LegibleBot vs CooperateBot, the whole FLOOR regime: the floor-blind
    moralist of transparency EXPLOITS the unconditional cooperator — below the
    size floor it cannot certify its own legibility, so it defects on
    principle. The non-floor regime is RESOLVED (2026-07-30): see the staggered large-`k` theorem below. -/
theorem outcome_LegibleBot_vs_CooperateBot_floor (kOut kIn fuel : Nat)
    (hsz : kOut < (Formula.box kIn
      (.plays (LegibleBot kOut kIn) CooperateBot .C)).size) :
    outcome (fuel + 2) (LegibleBot kOut kIn) CooperateBot = some (.D, .C) :=
  outcome_of_plays _ _ _ _ _ (LegibleBot_defects_floor kOut kIn fuel _ hsz)
    (play_CooperateBot (fuel + 1) _)

/-- The concrete `(2, 2)` instance. -/
theorem outcome_LegibleBot_vs_CooperateBot_floor2 (fuel : Nat) :
    outcome (fuel + 2) (LegibleBot 2 2) CooperateBot = some (.D, .C) :=
  outcome_LegibleBot_vs_CooperateBot_floor 2 2 fuel (by decide)

/-- **LegibleBot (staggered) vs CooperateBot: `(C, C)`** for all sufficiently
    large `k`. In the non-degenerate regime `LegibleBot (2k+64) k` the guard
    `□_k (I play C)` fits: bounded Löb through the two boxes (`searchBranch` +
    `box4` via `pblt_engine`) makes the cooperation legible and the guard fires;
    CooperateBot cooperates unconditionally. Staggered complement of
    `outcome_LegibleBot_vs_CooperateBot_floor`. -/
theorem outcome_LegibleBot_vs_CooperateBot :
    ∃ k₂, ∀ k, k > k₂ →
      ∃ fuel, outcome fuel (LegibleBot (2*k+64) k) CooperateBot = some (.C, .C) := by
  obtain ⟨k₂, h⟩ := LegibleBot_cooperates_large (fun _ => CooperateBot) 100
    (fun k => by
      show (CooperateBot).size ≤ 100 + 20 * Nat.log2 k
      simp only [CooperateBot, Prog.size]; omega)
  refine ⟨k₂, fun k hk => ?_⟩
  obtain ⟨n, hn⟩ := h k hk
  have hn' : eval n (LegibleBot (2*k+64) k) CooperateBot (LegibleBot (2*k+64) k)
      = some .C := hn
  have hL : play (n+1) (LegibleBot (2*k+64) k) CooperateBot = some .C :=
    eval_mono_le hn' (n+1) (Nat.le_succ n)
  exact ⟨n+1, outcome_of_plays _ _ _ _ _ hL (play_CooperateBot n _)⟩

end PD.Theorems
