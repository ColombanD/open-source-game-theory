import PrisonersDilemma.Program
import PrisonersDilemma.Dynamics
import PrisonersDilemma.Bots.LlmGenerations.LegibleBot
import PrisonersDilemma.Bots.OBot
import PrisonersDilemma.Bots.CooperateBot
import PrisonersDilemma.Base.Helpers
import PrisonersDilemma.BaseTheorems
import PrisonersDilemma.Theorems.LegibleBot.Helpers

open PD
open PD.BaseTheorems
open PD.Bots
namespace PD.Theorems

/-- LegibleBot vs OBot, the whole FLOOR regime: OBot's CooperateBot probe sees
    the floor-defection — mutual defection. The non-floor regime is RESOLVED (2026-07-30): see the staggered large-`k` theorem below. -/
theorem outcome_LegibleBot_vs_OBot_floor (kOut kIn fuel : Nat)
    (hszO : kOut < (Formula.box kIn
      (.plays (LegibleBot kOut kIn) OBot .C)).size)
    (hszCB : kOut < (Formula.box kIn
      (.plays (LegibleBot kOut kIn) (.bot CooperateBot) .C)).size) :
    outcome (fuel + 4) (LegibleBot kOut kIn) OBot = some (.D, .D) := by
  have hA : play (fuel + 4) (LegibleBot kOut kIn) OBot = some .D := by
    simpa [Nat.add_assoc] using
      LegibleBot_defects_floor kOut kIn (fuel + 2) OBot hszO
  exact outcome_of_plays _ _ _ _ _ hA
    (OBot_plays_D_against_LegibleBot_floor kOut kIn fuel hszCB)

/-- The concrete `(2, 2)` instance. -/
theorem outcome_LegibleBot_vs_OBot_floor2 (fuel : Nat) :
    outcome (fuel + 4) (LegibleBot 2 2) OBot = some (.D, .D) :=
  outcome_LegibleBot_vs_OBot_floor 2 2 fuel (by decide) (by decide)

/-- **LegibleBot (staggered) vs OBot: `(C, C)`** for all sufficiently large `k`.
    Both of OBot's probes (`.bot CooperateBot`, then `.bot DefectBot`) see the
    Löb-fired cooperation; OBot's nested `ite` forgives the
    cooperation-with-defectors and cooperates. Three core instantiations (live
    opponent + two probes), the inner `ite` peeled by `eval_ite_from_guard`.
    Staggered complement of `outcome_LegibleBot_vs_OBot_floor`. -/
theorem outcome_LegibleBot_vs_OBot :
    ∃ k₂, ∀ k, k > k₂ →
      ∃ fuel, outcome fuel (LegibleBot (2*k+64) k) OBot = some (.C, .C) := by
  obtain ⟨kA, hA⟩ := LegibleBot_cooperates_large (fun _ => OBot) 100
    (fun k => by
      show (OBot).size ≤ 100 + 20 * Nat.log2 k
      simp only [OBot, CooperateBot, DefectBot, Prog.size]; omega)
  obtain ⟨kB, hB⟩ := LegibleBot_cooperates_large (fun _ => .bot CooperateBot) 100
    (fun k => by
      show (Prog.bot CooperateBot).size ≤ 100 + 20 * Nat.log2 k
      simp only [CooperateBot, Prog.size]; omega)
  obtain ⟨kC, hC⟩ := LegibleBot_cooperates_large (fun _ => .bot DefectBot) 100
    (fun k => by
      show (Prog.bot DefectBot).size ≤ 100 + 20 * Nat.log2 k
      simp only [DefectBot, Prog.size]; omega)
  refine ⟨max kA (max kB kC), fun k hk => ?_⟩
  obtain ⟨n₁, hn₁⟩ := hA k (lt_of_le_of_lt (Nat.le_max_left _ _) hk)
  obtain ⟨n₂, hn₂⟩ := hB k (lt_of_le_of_lt
    (Nat.le_trans (Nat.le_max_left _ _) (Nat.le_max_right _ _)) hk)
  obtain ⟨n₃, hn₃⟩ := hC k (lt_of_le_of_lt
    (Nat.le_trans (Nat.le_max_right _ _) (Nat.le_max_right _ _)) hk)
  set N := max n₁ (max n₂ n₃) with hN
  have hle₁ : n₁ ≤ N := Nat.le_max_left _ _
  have hle₂ : n₂ ≤ N := Nat.le_trans (Nat.le_max_left _ _) (Nat.le_max_right _ _)
  have hle₃ : n₃ ≤ N := Nat.le_trans (Nat.le_max_right _ _) (Nat.le_max_right _ _)
  have hn₁' : eval n₁ (LegibleBot (2*k+64) k) OBot (LegibleBot (2*k+64) k)
      = some .C := hn₁
  have hL : play (N + 3) (LegibleBot (2*k+64) k) OBot = some .C :=
    eval_mono_le hn₁' _ (Nat.le_trans hle₁ (Nat.le_add_right _ 3))
  have hprobeCB : play N (LegibleBot (2*k+64) k) (.bot CooperateBot) = some .C := by
    have h' : eval n₂ (LegibleBot (2*k+64) k) (.bot CooperateBot) (LegibleBot (2*k+64) k)
        = some .C := hn₂
    exact eval_mono_le h' _ hle₂
  have hprobeDB : play N (LegibleBot (2*k+64) k) (.bot DefectBot) = some .C := by
    have h' : eval n₃ (LegibleBot (2*k+64) k) (.bot DefectBot) (LegibleBot (2*k+64) k)
        = some .C := hn₃
    exact eval_mono_le h' _ hle₃
  have hG1 : eval (N + 1) OBot (LegibleBot (2*k+64) k)
      (.sim .opp (.bot CooperateBot)) = some .C :=
    eval_sim_opp_bot_of_play N OBot (LegibleBot (2*k+64) k) CooperateBot .C hprobeCB
  have hG1' : eval (N + 2) OBot (LegibleBot (2*k+64) k)
      (.sim .opp (.bot CooperateBot)) = some .C :=
    eval_mono_le hG1 _ (Nat.le_succ _)
  have hG2 : eval (N + 1) OBot (LegibleBot (2*k+64) k)
      (.sim .opp (.bot DefectBot)) = some .C :=
    eval_sim_opp_bot_of_play N OBot (LegibleBot (2*k+64) k) DefectBot .C hprobeDB
  have hInner : eval (N + 2) OBot (LegibleBot (2*k+64) k)
      (.ite (.sim .opp (.bot DefectBot)) .C (.const .C) (.const .D)) = some .C := by
    have h := eval_ite_from_guard (N + 1) OBot (LegibleBot (2*k+64) k)
      (.sim .opp (.bot DefectBot)) (.const .C) (.const .D) .C .C hG2
    simpa [eval] using h
  have hO := play_ite_from_guard N 2 OBot (LegibleBot (2*k+64) k)
    (.sim .opp (.bot CooperateBot))
    (.ite (.sim .opp (.bot DefectBot)) .C (.const .C) (.const .D)) (.const .D)
    .C .C rfl hG1'
  have hO' : play (N + 3) OBot (LegibleBot (2*k+64) k) = some .C := by
    rw [show N + 2 + 1 = N + 3 by omega] at hO
    rw [hO]
    simpa using hInner
  exact ⟨N + 3, outcome_of_plays _ _ _ _ _ hL hO'⟩

end PD.Theorems
