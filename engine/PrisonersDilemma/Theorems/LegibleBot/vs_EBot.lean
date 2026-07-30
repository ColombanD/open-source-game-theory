import PrisonersDilemma.Program
import PrisonersDilemma.Dynamics
import PrisonersDilemma.Bots.LlmGenerations.LegibleBot
import PrisonersDilemma.Bots.EBot
import PrisonersDilemma.Bots.CooperateBot
import PrisonersDilemma.Bots.DefectBot
import PrisonersDilemma.Bots.MirrorBot
import PrisonersDilemma.Base.Helpers
import PrisonersDilemma.BaseTheorems
import PrisonersDilemma.Theorems.LegibleBot.Helpers

open PD
open PD.BaseTheorems
open PD.Bots
namespace PD.Theorems

/-- LegibleBot vs EBot, the whole FLOOR regime: all three of EBot's probes see
    the floor-defection — mutual defection. The non-floor regime is RESOLVED (2026-07-30): see the staggered large-`k` theorem below. -/
theorem outcome_LegibleBot_vs_EBot_floor (kOut kIn fuel : Nat)
    (hszE : kOut < (Formula.box kIn
      (.plays (LegibleBot kOut kIn) EBot .C)).size)
    (hszDB : kOut < (Formula.box kIn
      (.plays (LegibleBot kOut kIn) (.bot DefectBot) .C)).size)
    (hszCB : kOut < (Formula.box kIn
      (.plays (LegibleBot kOut kIn) (.bot CooperateBot) .C)).size)
    (hszM : kOut < (Formula.box kIn
      (.plays (LegibleBot kOut kIn) (.bot MirrorBot) .C)).size) :
    outcome (fuel + 6) (LegibleBot kOut kIn) EBot = some (.D, .D) := by
  have hA : play (fuel + 6) (LegibleBot kOut kIn) EBot = some .D := by
    simpa [Nat.add_assoc] using
      LegibleBot_defects_floor kOut kIn (fuel + 4) EBot hszE
  exact outcome_of_plays _ _ _ _ _ hA
    (EBot_plays_D_against_LegibleBot_floor kOut kIn fuel hszDB hszCB hszM)

/-- The concrete `(2, 2)` instance. -/
theorem outcome_LegibleBot_vs_EBot_floor2 (fuel : Nat) :
    outcome (fuel + 6) (LegibleBot 2 2) EBot = some (.D, .D) :=
  outcome_LegibleBot_vs_EBot_floor 2 2 fuel
    (by decide) (by decide) (by decide) (by decide)

/-- **LegibleBot (staggered) vs EBot: `(C, D)`** for all sufficiently large `k`.
    EBot's FIRST probe (`.bot DefectBot`) sees the opponent-blind Löb
    cooperation and EBot defects immediately — the nested CooperateBot/MirrorBot
    probes are never consulted. Same exploitation pattern as DBot. Staggered
    complement of `outcome_LegibleBot_vs_EBot_floor`. -/
theorem outcome_LegibleBot_vs_EBot :
    ∃ k₂, ∀ k, k > k₂ →
      ∃ fuel, outcome fuel (LegibleBot (2*k+64) k) EBot = some (.C, .D) := by
  obtain ⟨kA, hA⟩ := LegibleBot_cooperates_large (fun _ => EBot) 100
    (fun k => by
      show (EBot).size ≤ 100 + 20 * Nat.log2 k
      simp only [EBot, DefectBot, CooperateBot, MirrorBot, Prog.size]; omega)
  obtain ⟨kB, hB⟩ := LegibleBot_cooperates_large (fun _ => .bot DefectBot) 100
    (fun k => by
      show (Prog.bot DefectBot).size ≤ 100 + 20 * Nat.log2 k
      simp only [DefectBot, Prog.size]; omega)
  refine ⟨max kA kB, fun k hk => ?_⟩
  obtain ⟨n₁, hn₁⟩ := hA k (lt_of_le_of_lt (Nat.le_max_left _ _) hk)
  obtain ⟨n₂, hn₂⟩ := hB k (lt_of_le_of_lt (Nat.le_max_right _ _) hk)
  have hn₁' : eval n₁ (LegibleBot (2*k+64) k) EBot (LegibleBot (2*k+64) k)
      = some .C := hn₁
  have hL : play (max n₁ n₂ + 2) (LegibleBot (2*k+64) k) EBot = some .C :=
    eval_mono_le hn₁' _ (Nat.le_trans (Nat.le_max_left _ _) (Nat.le_add_right _ 2))
  have hprobe : play (max n₁ n₂) (LegibleBot (2*k+64) k) (.bot DefectBot) = some .C := by
    have hn₂' : eval n₂ (LegibleBot (2*k+64) k) (.bot DefectBot) (LegibleBot (2*k+64) k)
        = some .C := hn₂
    exact eval_mono_le hn₂' _ (Nat.le_max_right _ _)
  have hGuard : eval (max n₁ n₂ + 1) EBot (LegibleBot (2*k+64) k)
      (.sim .opp (.bot DefectBot)) = some .C :=
    eval_sim_opp_bot_of_play (max n₁ n₂) EBot (LegibleBot (2*k+64) k)
      DefectBot .C hprobe
  have hE := play_ite_from_guard (max n₁ n₂) 1 EBot (LegibleBot (2*k+64) k)
    (.sim .opp (.bot DefectBot)) (.const .D)
    (.ite (.sim .opp (.bot CooperateBot)) .C (.const .C)
      (.ite (.sim .opp (.bot MirrorBot)) .C (.const .C) (.const .D)))
    .C .C rfl hGuard
  have hE' : play (max n₁ n₂ + 2) EBot (LegibleBot (2*k+64) k) = some .D := by
    simpa [eval] using hE
  exact ⟨max n₁ n₂ + 2, outcome_of_plays _ _ _ _ _ hL hE'⟩

end PD.Theorems
