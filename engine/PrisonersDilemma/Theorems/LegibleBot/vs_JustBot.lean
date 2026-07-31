import PrisonersDilemma.Bots.LlmGenerations.LegibleBot
import PrisonersDilemma.Bots.LlmGenerations.JustBot
import PrisonersDilemma.Bots.DupocBot
import PrisonersDilemma.Base.Helpers
import PrisonersDilemma.BaseTheorems
import PrisonersDilemma.Theorems.LegibleBot.Helpers
import PrisonersDilemma.Theorems.JustBot.Helpers

open PD
open PD.BaseTheorems
open PD.Bots
namespace PD.Theorems

theorem llm_outcome_LegibleBot_vs_JustBot :
    ∃ k₂, ∀ k, k₂ < k →
      ∃ fuel, outcome fuel (LegibleBot (2*k+64) k) (JustBot k) = some (.C, .C) := by
  obtain ⟨kA, hA⟩ := LegibleBot_cooperates_large (fun k => JustBot k) 100
    (fun k => by
      show (JustBot k).size ≤ 100 + 20 * Nat.log2 k
      simp only [JustBot, DupocBot, Prog.size, Formula.size, numCost]; omega)
  obtain ⟨kB, hB⟩ := LegibleBot_cooperates_large (fun k => .bot (DupocBot k)) 100
    (fun k => by
      show (Prog.bot (DupocBot k)).size ≤ 100 + 20 * Nat.log2 k
      simp only [DupocBot, Prog.size, Formula.size, numCost]; omega)
  obtain ⟨K, hK⟩ := linear_log2_add_le 20 500
  refine ⟨max (max kA kB) K, fun k hk => ?_⟩
  obtain ⟨n, hn⟩ := hA k (lt_of_le_of_lt (Nat.le_max_left _ _) (lt_of_le_of_lt (Nat.le_max_left _ _) hk))
  obtain ⟨n', hn'⟩ := hB k (lt_of_le_of_lt (Nat.le_max_right _ _) (lt_of_le_of_lt (Nat.le_max_left _ _) hk))
  have hbox : Pf (2*k+64) (.box k (.plays (LegibleBot (2*k+64) k) (.bot (DupocBot k)) .C)) :=
    LegibleBot_playC_gives_box k n' (.bot (DupocBot k)) hn'
  -- Cheap atom certificate for LegibleBot plays C vs .bot (DupocBot k), at budget k
  have hatom : AtomProvable (c_leaf + c_guard (2*k+64) + c_node)
      (.plays (LegibleBot (2*k+64) k) (.bot (DupocBot k)) .C) :=
    ⟨PlaysProof.search_t hbox PlaysProof.const, Nat.le_refl _⟩
  have hatomK : AtomProvable k (.plays (LegibleBot (2*k+64) k) (.bot (DupocBot k)) .C) := by
    refine atom_monotone _ k _ ?_ hatom
    have hKk := hK k (Nat.le_of_lt (lt_of_le_of_lt (Nat.le_max_right _ _) hk))
    have hst := log2_stagger_le k
    simp only [c_leaf, c_node, c_guard, numCost]
    omega
  -- JustBot's guard fires
  have hguard : proofSearch k
      (Formula.plays (LegibleBot (2*k+64) k) (.bot (DupocBot k)) Action.C) = true :=
    (proofSearch_spec _ _).2 (Pf.atom hatomK)
  -- JustBot plays C
  have hJust : play (n + 2) (JustBot k) (LegibleBot (2*k+64) k) = some .C := by
    refine JustBot_eval_step k n (LegibleBot (2*k+64) k) .C ?_
    simp only [hguard]; rfl
  have hLeg : play (n + 2) (LegibleBot (2*k+64) k) (JustBot k) = some .C :=
    eval_mono_le hn _ (Nat.le_add_right _ _)
  exact ⟨n + 2, outcome_of_plays _ _ _ _ _ hLeg hJust⟩

end PD.Theorems

