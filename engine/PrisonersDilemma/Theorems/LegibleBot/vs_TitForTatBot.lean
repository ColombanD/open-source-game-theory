import PrisonersDilemma.Program
import PrisonersDilemma.Dynamics
import PrisonersDilemma.Bots.LlmGenerations.LegibleBot
import PrisonersDilemma.Bots.TitForTatBot
import PrisonersDilemma.Bots.CooperateBot
import PrisonersDilemma.Base.Helpers
import PrisonersDilemma.BaseTheorems
import PrisonersDilemma.Theorems.LegibleBot.Helpers

open PD
open PD.BaseTheorems
open PD.Bots
namespace PD.Theorems

/-- LegibleBot vs TitForTatBot, the whole FLOOR regime: TFT's probe sees the
    floor-defection and punishes — mutual defection. The non-floor regime is RESOLVED (2026-07-30): see the staggered large-`k` theorem below. -/
theorem outcome_LegibleBot_vs_TitForTatBot_floor (kOut kIn fuel : Nat)
    (hszT : kOut < (Formula.box kIn
      (.plays (LegibleBot kOut kIn) TitForTatBot .C)).size)
    (hszCB : kOut < (Formula.box kIn
      (.plays (LegibleBot kOut kIn) (.bot CooperateBot) .C)).size) :
    outcome (fuel + 4) (LegibleBot kOut kIn) TitForTatBot = some (.D, .D) := by
  have hA : play (fuel + 4) (LegibleBot kOut kIn) TitForTatBot = some .D := by
    simpa [Nat.add_assoc] using
      LegibleBot_defects_floor kOut kIn (fuel + 2) TitForTatBot hszT
  exact outcome_of_plays _ _ _ _ _ hA
    (TitForTatBot_plays_D_against_LegibleBot_floor kOut kIn fuel hszCB)

/-- The concrete `(2, 2)` instance. -/
theorem outcome_LegibleBot_vs_TitForTatBot_floor2 (fuel : Nat) :
    outcome (fuel + 4) (LegibleBot 2 2) TitForTatBot = some (.D, .D) :=
  outcome_LegibleBot_vs_TitForTatBot_floor 2 2 fuel (by decide) (by decide)

/-- **LegibleBot (staggered) vs TitForTatBot: `(C, C)`** for all sufficiently
    large `k`. The Löb core is opponent-generic, so it fires equally against
    TitForTatBot's `.bot CooperateBot` probe: the probe sees the legible
    cooperation and TFT reciprocates. Two core instantiations (the live opponent
    and the probe), joined at a common fuel. Staggered complement of
    `outcome_LegibleBot_vs_TitForTatBot_floor`. -/
theorem outcome_LegibleBot_vs_TitForTatBot :
    ∃ k₂, ∀ k, k > k₂ →
      ∃ fuel, outcome fuel (LegibleBot (2*k+64) k) TitForTatBot = some (.C, .C) := by
  obtain ⟨kA, hA⟩ := LegibleBot_cooperates_large (fun _ => TitForTatBot) 100
    (fun k => by
      show (TitForTatBot).size ≤ 100 + 20 * Nat.log2 k
      simp only [TitForTatBot, CooperateBot, Prog.size]; omega)
  obtain ⟨kB, hB⟩ := LegibleBot_cooperates_large (fun _ => .bot CooperateBot) 100
    (fun k => by
      show (Prog.bot CooperateBot).size ≤ 100 + 20 * Nat.log2 k
      simp only [CooperateBot, Prog.size]; omega)
  refine ⟨max kA kB, fun k hk => ?_⟩
  obtain ⟨n₁, hn₁⟩ := hA k (lt_of_le_of_lt (Nat.le_max_left _ _) hk)
  obtain ⟨n₂, hn₂⟩ := hB k (lt_of_le_of_lt (Nat.le_max_right _ _) hk)
  have hn₁' : eval n₁ (LegibleBot (2*k+64) k) TitForTatBot (LegibleBot (2*k+64) k)
      = some .C := hn₁
  have hL : play (max n₁ n₂ + 2) (LegibleBot (2*k+64) k) TitForTatBot = some .C :=
    eval_mono_le hn₁' _ (Nat.le_trans (Nat.le_max_left _ _) (Nat.le_add_right _ 2))
  have hprobe : play (max n₁ n₂) (LegibleBot (2*k+64) k) (.bot CooperateBot) = some .C := by
    have hn₂' : eval n₂ (LegibleBot (2*k+64) k) (.bot CooperateBot) (LegibleBot (2*k+64) k)
        = some .C := hn₂
    exact eval_mono_le hn₂' _ (Nat.le_max_right _ _)
  have hGuard : eval (max n₁ n₂ + 1) TitForTatBot (LegibleBot (2*k+64) k)
      (.sim .opp (.bot CooperateBot)) = some .C :=
    eval_sim_opp_bot_of_play (max n₁ n₂) TitForTatBot (LegibleBot (2*k+64) k)
      CooperateBot .C hprobe
  have hT := play_ite_from_guard (max n₁ n₂) 1 TitForTatBot (LegibleBot (2*k+64) k)
    (.sim .opp (.bot CooperateBot)) (.const .C) (.const .D) .C .C rfl hGuard
  have hT' : play (max n₁ n₂ + 2) TitForTatBot (LegibleBot (2*k+64) k) = some .C := by
    simpa [eval] using hT
  exact ⟨max n₁ n₂ + 2, outcome_of_plays _ _ _ _ _ hL hT'⟩

end PD.Theorems
