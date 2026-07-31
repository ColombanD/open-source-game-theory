import PrisonersDilemma.Program
import PrisonersDilemma.Dynamics
import PrisonersDilemma.Bots.LlmGenerations.LegibleBot
import PrisonersDilemma.Bots.DupocBot
import PrisonersDilemma.Base.Helpers
import PrisonersDilemma.BaseTheorems
import PrisonersDilemma.Theorems.LegibleBot.Helpers

open PD
open PD.BaseTheorems
open PD.Bots
namespace PD.Theorems

theorem llm_outcome_LegibleBot_vs_DupocBot :
    ∃ k₂, ∀ k, k₂ < k →
      ∃ fuel, outcome fuel (LegibleBot (2*k+64) k) (DupocBot k) = some (.C, .C) := by
  obtain ⟨kA, hA⟩ := LegibleBot_cooperates_large (fun k => DupocBot k) 100
    (fun k => by simp only [DupocBot, Prog.size, Formula.size, numCost]; omega)
  obtain ⟨K, hK⟩ := linear_log2_add_le 20 500
  refine ⟨max kA K, fun k hk => ?_⟩
  obtain ⟨n, hn⟩ := hA k (lt_of_le_of_lt (Nat.le_max_left _ _) hk)
  have hbox : Pf (2*k+64) (.box k (.plays (LegibleBot (2*k+64) k) (DupocBot k) .C)) :=
    LegibleBot_playC_gives_box k n (DupocBot k) hn
  have hatom : AtomProvable (c_leaf + c_guard (2*k+64) + c_node)
      (.plays (LegibleBot (2*k+64) k) (DupocBot k) .C) :=
    ⟨PlaysProof.search_t hbox PlaysProof.const, Nat.le_refl _⟩
  have hguardD : Pf k (.plays (LegibleBot (2*k+64) k) (DupocBot k) .C) := by
    refine Pf.atom (atom_monotone _ k _ ?_ hatom)
    have hKk := hK k (Nat.le_of_lt (lt_of_le_of_lt (Nat.le_max_right _ _) hk))
    have hst := log2_stagger_le k
    simp only [c_leaf, c_node, c_guard, numCost]
    omega
  have hps : proofSearch k
      (.plays (LegibleBot (2*k+64) k) (DupocBot k) Action.C) = true :=
    (proofSearch_spec _ _).2 hguardD
  have hDplay : play (n + 2) (DupocBot k) (LegibleBot (2*k+64) k) = some .C := by
    show eval (n + 2) (DupocBot k) (LegibleBot (2*k+64) k) (DupocBot k) = some .C
    conv_lhs => unfold DupocBot
    simp only [eval, Prog.subst, Formula.subst]
    rw [show (Prog.search k (Formula.plays Prog.opp Prog.self Action.C)
              (Prog.const Action.C) (Prog.const Action.D)) = DupocBot k from rfl]
    rw [hps]; rfl
  have hn' : eval n (LegibleBot (2*k+64) k) (DupocBot k) (LegibleBot (2*k+64) k)
      = some .C := hn
  have hLplay : play (n + 2) (LegibleBot (2*k+64) k) (DupocBot k) = some .C :=
    eval_mono_le hn' _ (Nat.le_add_right _ 2)
  exact ⟨n + 2, outcome_of_plays _ _ _ _ _ hLplay hDplay⟩

end PD.Theorems
