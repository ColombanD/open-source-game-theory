import PrisonersDilemma.Program
import PrisonersDilemma.Dynamics
import PrisonersDilemma.Bots.LlmGenerations.LegibleBot
import PrisonersDilemma.Bots.MirrorBot
import PrisonersDilemma.Base.Helpers
import PrisonersDilemma.BaseTheorems
import PrisonersDilemma.Theorems.LegibleBot.Helpers

open PD
open PD.BaseTheorems
open PD.Bots
namespace PD.Theorems

/-- LegibleBot vs MirrorBot, the whole FLOOR regime: the mirror replays the
    floor-defection — mutual defection. The non-floor regime is RESOLVED (2026-07-30): see the staggered large-`k` theorem below. -/
theorem outcome_LegibleBot_vs_MirrorBot_floor (kOut kIn fuel : Nat)
    (hszM : kOut < (Formula.box kIn
      (.plays (LegibleBot kOut kIn) MirrorBot .C)).size) :
    outcome (fuel + 3) (LegibleBot kOut kIn) MirrorBot = some (.D, .D) := by
  have hA : play (fuel + 3) (LegibleBot kOut kIn) MirrorBot = some .D := by
    simpa [Nat.add_assoc] using
      LegibleBot_defects_floor kOut kIn (fuel + 1) MirrorBot hszM
  exact outcome_of_plays _ _ _ _ _ hA
    (MirrorBot_plays_D_against_LegibleBot_floor kOut kIn fuel hszM)

/-- The concrete `(2, 2)` instance. -/
theorem outcome_LegibleBot_vs_MirrorBot_floor2 (fuel : Nat) :
    outcome (fuel + 3) (LegibleBot 2 2) MirrorBot = some (.D, .D) :=
  outcome_LegibleBot_vs_MirrorBot_floor 2 2 fuel (by decide)

/-- **LegibleBot (staggered) vs MirrorBot: `(C, C)`** for all sufficiently large
    `k`. The Löb-fired cooperation is replayed by the mirror: MirrorBot's
    `.sim .opp .self` runs LegibleBot against MirrorBot, which is exactly the
    play the engine certified. Staggered complement of
    `outcome_LegibleBot_vs_MirrorBot_floor` (where the mirror replays defection). -/
theorem outcome_LegibleBot_vs_MirrorBot :
    ∃ k₂, ∀ k, k > k₂ →
      ∃ fuel, outcome fuel (LegibleBot (2*k+64) k) MirrorBot = some (.C, .C) := by
  obtain ⟨k₂, h⟩ := LegibleBot_cooperates_large (fun _ => MirrorBot) 100
    (fun k => by
      show (MirrorBot).size ≤ 100 + 20 * Nat.log2 k
      simp only [MirrorBot, Prog.size]; omega)
  refine ⟨k₂, fun k hk => ?_⟩
  obtain ⟨n, hn⟩ := h k hk
  have hn' : eval n (LegibleBot (2*k+64) k) MirrorBot (LegibleBot (2*k+64) k)
      = some .C := hn
  have hL : play (n+1) (LegibleBot (2*k+64) k) MirrorBot = some .C :=
    eval_mono_le hn' (n+1) (Nat.le_succ n)
  have hM : play (n+1) MirrorBot (LegibleBot (2*k+64) k) = some .C := by
    show eval (n+1) MirrorBot (LegibleBot (2*k+64) k) MirrorBot = some .C
    simpa [eval, MirrorBot, Prog.subst] using hn
  exact ⟨n+1, outcome_of_plays _ _ _ _ _ hL hM⟩

end PD.Theorems
