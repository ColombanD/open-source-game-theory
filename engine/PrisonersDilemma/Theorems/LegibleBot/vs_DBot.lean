import PrisonersDilemma.Program
import PrisonersDilemma.Dynamics
import PrisonersDilemma.Bots.LlmGenerations.LegibleBot
import PrisonersDilemma.Bots.DBot
import PrisonersDilemma.Bots.DefectBot
import PrisonersDilemma.Base.Helpers
import PrisonersDilemma.BaseTheorems
import PrisonersDilemma.Theorems.LegibleBot.Helpers

open PD
open PD.BaseTheorems
open PD.Bots
namespace PD.Theorems

/-- LegibleBot vs DBot, the whole FLOOR regime: DBot only exploits bots that
    cooperate with defectors; the floor-defector is spared and DBot cooperates —
    `(D, C)`. The non-floor regime is RESOLVED (2026-07-30): see the staggered large-`k` theorem below. -/
theorem outcome_LegibleBot_vs_DBot_floor (kOut kIn fuel : Nat)
    (hszD : kOut < (Formula.box kIn
      (.plays (LegibleBot kOut kIn) DBot .C)).size)
    (hszDB : kOut < (Formula.box kIn
      (.plays (LegibleBot kOut kIn) (.bot DefectBot) .C)).size) :
    outcome (fuel + 4) (LegibleBot kOut kIn) DBot = some (.D, .C) := by
  have hA : play (fuel + 4) (LegibleBot kOut kIn) DBot = some .D := by
    simpa [Nat.add_assoc] using
      LegibleBot_defects_floor kOut kIn (fuel + 2) DBot hszD
  exact outcome_of_plays _ _ _ _ _ hA
    (DBot_plays_C_against_LegibleBot_floor kOut kIn fuel hszDB)

/-- The concrete `(2, 2)` instance. -/
theorem outcome_LegibleBot_vs_DBot_floor2 (fuel : Nat) :
    outcome (fuel + 4) (LegibleBot 2 2) DBot = some (.D, .C) :=
  outcome_LegibleBot_vs_DBot_floor 2 2 fuel (by decide) (by decide)

/-- **LegibleBot (staggered) vs DBot: `(C, D)`** for all sufficiently large `k`.
    DBot exploits exactly the bots that cooperate with defectors: LegibleBot's
    opponent-blind Löb cooperation fires even against the `.bot DefectBot`
    probe, so the defection-detector defects. Inverse of the floor regime
    (`outcome_LegibleBot_vs_DBot_floor = (D, C)`), where the floor-defector was
    spared. -/
theorem outcome_LegibleBot_vs_DBot :
    ∃ k₂, ∀ k, k > k₂ →
      ∃ fuel, outcome fuel (LegibleBot (2*k+64) k) DBot = some (.C, .D) := by
  obtain ⟨kA, hA⟩ := LegibleBot_cooperates_large (fun _ => DBot) 100
    (fun k => by
      show (DBot).size ≤ 100 + 20 * Nat.log2 k
      simp only [DBot, DefectBot, Prog.size]; omega)
  obtain ⟨kB, hB⟩ := LegibleBot_cooperates_large (fun _ => .bot DefectBot) 100
    (fun k => by
      show (Prog.bot DefectBot).size ≤ 100 + 20 * Nat.log2 k
      simp only [DefectBot, Prog.size]; omega)
  refine ⟨max kA kB, fun k hk => ?_⟩
  obtain ⟨n₁, hn₁⟩ := hA k (lt_of_le_of_lt (Nat.le_max_left _ _) hk)
  obtain ⟨n₂, hn₂⟩ := hB k (lt_of_le_of_lt (Nat.le_max_right _ _) hk)
  have hn₁' : eval n₁ (LegibleBot (2*k+64) k) DBot (LegibleBot (2*k+64) k)
      = some .C := hn₁
  have hL : play (max n₁ n₂ + 2) (LegibleBot (2*k+64) k) DBot = some .C :=
    eval_mono_le hn₁' _ (Nat.le_trans (Nat.le_max_left _ _) (Nat.le_add_right _ 2))
  have hprobe : play (max n₁ n₂) (LegibleBot (2*k+64) k) (.bot DefectBot) = some .C := by
    have hn₂' : eval n₂ (LegibleBot (2*k+64) k) (.bot DefectBot) (LegibleBot (2*k+64) k)
        = some .C := hn₂
    exact eval_mono_le hn₂' _ (Nat.le_max_right _ _)
  have hGuard : eval (max n₁ n₂ + 1) DBot (LegibleBot (2*k+64) k)
      (.sim .opp (.bot DefectBot)) = some .C :=
    eval_sim_opp_bot_of_play (max n₁ n₂) DBot (LegibleBot (2*k+64) k)
      DefectBot .C hprobe
  have hD := play_ite_from_guard (max n₁ n₂) 1 DBot (LegibleBot (2*k+64) k)
    (.sim .opp (.bot DefectBot)) (.const .D) (.const .C) .C .C rfl hGuard
  have hD' : play (max n₁ n₂ + 2) DBot (LegibleBot (2*k+64) k) = some .D := by
    simpa [eval] using hD
  exact ⟨max n₁ n₂ + 2, outcome_of_plays _ _ _ _ _ hL hD'⟩

end PD.Theorems
