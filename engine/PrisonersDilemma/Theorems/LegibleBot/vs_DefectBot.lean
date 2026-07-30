import PrisonersDilemma.Program
import PrisonersDilemma.Dynamics
import PrisonersDilemma.Bots.LlmGenerations.LegibleBot
import PrisonersDilemma.Bots.DefectBot
import PrisonersDilemma.Theorems.DefectBot.Helpers
import PrisonersDilemma.Base.Helpers
import PrisonersDilemma.BaseTheorems
import PrisonersDilemma.Theorems.LegibleBot.Helpers

open PD
open PD.BaseTheorems
open PD.Bots
namespace PD.Theorems

/-- LegibleBot vs DefectBot, the whole FLOOR regime: mutual defection.
    The non-floor regime is RESOLVED (2026-07-30): see the staggered large-`k` theorem below. -/
theorem outcome_LegibleBot_vs_DefectBot_floor (kOut kIn fuel : Nat)
    (hsz : kOut < (Formula.box kIn
      (.plays (LegibleBot kOut kIn) DefectBot .C)).size) :
    outcome (fuel + 2) (LegibleBot kOut kIn) DefectBot = some (.D, .D) :=
  outcome_of_plays _ _ _ _ _ (LegibleBot_defects_floor kOut kIn fuel _ hsz)
    (play_DefectBot (fuel + 1) _)

/-- The concrete `(2, 2)` instance. -/
theorem outcome_LegibleBot_vs_DefectBot_floor2 (fuel : Nat) :
    outcome (fuel + 2) (LegibleBot 2 2) DefectBot = some (.D, .D) :=
  outcome_LegibleBot_vs_DefectBot_floor 2 2 fuel (by decide)

/-- **LegibleBot (staggered) vs DefectBot: `(C, D)`** for all sufficiently large
    `k`. LegibleBot's guard is about its OWN transparency, not the opponent's
    behaviour — bounded Löb fires it against anyone, so the legible cooperator
    is exploited by the unconditional defector. The price of opponent-blind
    legibility; staggered complement of `outcome_LegibleBot_vs_DefectBot_floor`. -/
theorem outcome_LegibleBot_vs_DefectBot :
    ∃ k₂, ∀ k, k > k₂ →
      ∃ fuel, outcome fuel (LegibleBot (2*k+64) k) DefectBot = some (.C, .D) := by
  obtain ⟨k₂, h⟩ := LegibleBot_cooperates_large (fun _ => DefectBot) 100
    (fun k => by
      show (DefectBot).size ≤ 100 + 20 * Nat.log2 k
      simp only [DefectBot, Prog.size]; omega)
  refine ⟨k₂, fun k hk => ?_⟩
  obtain ⟨n, hn⟩ := h k hk
  have hn' : eval n (LegibleBot (2*k+64) k) DefectBot (LegibleBot (2*k+64) k)
      = some .C := hn
  have hL : play (n+1) (LegibleBot (2*k+64) k) DefectBot = some .C :=
    eval_mono_le hn' (n+1) (Nat.le_succ n)
  exact ⟨n+1, outcome_of_plays _ _ _ _ _ hL (play_DefectBot n _)⟩

end PD.Theorems
