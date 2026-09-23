import PrisonersDilemma.Bots.LlmGenerations.OptimBot
import PrisonersDilemma.Bots.OBot
import PrisonersDilemma.Bots.CooperateBot
import PrisonersDilemma.Bots.DefectBot
import PrisonersDilemma.Dynamics
import PrisonersDilemma.Base.Helpers
import PrisonersDilemma.BaseTheorems
import PrisonersDilemma.Base.Asymptotics

open PD
open PD.Bots
open PD.BaseTheorems
namespace PD.Theorems

theorem oo_OBot_D_atomprov (k K : Nat)
    (hg1 : Pf k (Formula.plays (.bot CooperateBot) (OptimBot k K) Action.C))
    (hg2 : Pf K (Formula.plays (OptimBot k K) (.bot CooperateBot) Action.D)) :
    AtomProvable (2 * c_leaf + c_guard K + c_guard k + 4 * c_node)
      (.plays OBot (OptimBot k K) Action.D) := by
  have hinner : PlaysProof (OptimBot k K) (.bot CooperateBot) (OptimBot k K) Action.D
      (c_leaf + c_guard K + c_node + c_guard k + c_node) := by
    have : (OptimBot k K) = Prog.search k (Formula.plays Prog.opp Prog.self Action.C)
        (Prog.search K (Formula.plays Prog.self Prog.opp Action.D)
          (Prog.const Action.D) _) _ := rfl
    rw [this]
    refine PlaysProof.search_t ?_ (PlaysProof.search_t ?_ PlaysProof.const)
    · simpa [Formula.subst, Prog.subst] using hg1
    · simpa [Formula.subst, Prog.subst] using hg2
  have hprobe : PlaysProof OBot (OptimBot k K) (.sim .opp (.bot CooperateBot)) Action.D
      (c_leaf + c_guard K + c_node + c_guard k + c_node + c_node) := by
    refine PlaysProof.sim ?_
    simpa [Prog.subst] using hinner
  have hcert : PlaysProof OBot (OptimBot k K)
      (.ite (.sim .opp (.bot CooperateBot)) Action.C
        (.ite (.sim .opp (.bot DefectBot)) Action.C (.const Action.C) (.const Action.D))
        (.const Action.D)) Action.D
      (c_leaf + c_guard K + c_node + c_guard k + c_node + c_node
        + c_leaf + c_node) :=
    PlaysProof.ite_f hprobe (by decide) PlaysProof.const
  refine ⟨hcert, ?_⟩
  simp only [c_leaf, c_node]; omega

theorem oo_boxD (k K : Nat) (hnk : Nat.log2 K + Nat.log2 k + 8 ≤ k)
    (hg1 : Pf k (Formula.plays (.bot CooperateBot) (OptimBot k K) Action.C))
    (hg2 : Pf K (Formula.plays (OptimBot k K) (.bot CooperateBot) Action.D)) :
    Pf (300 * (Nat.log2 k + Nat.log2 K) + 50000)
       (.box k (.plays OBot (OptimBot k K) Action.D)) := by
  have hcert := oo_OBot_D_atomprov k K hg1 hg2
  have hn0le : 2 * c_leaf + c_guard K + c_guard k + 4 * c_node ≤ k := by
    simp only [c_leaf, c_guard, c_node, numCost]; omega
  have hln0 : Nat.log2 (2 * c_leaf + c_guard K + c_guard k + 4 * c_node)
      ≤ Nat.log2 k + Nat.log2 K + 8 := by
    have := log2_le_self (2 * c_leaf + c_guard K + c_guard k + 4 * c_node)
    simp only [c_leaf, c_guard, c_node, numCost] at this ⊢
    omega
  have hb1 : Pf (100 * (Nat.log2 k + Nat.log2 K) + 20000)
      (.box (2 * c_leaf + c_guard K + c_guard k + 4 * c_node)
        (.plays OBot (OptimBot k K) Action.D)) := by
    refine Pf.boxIntro _ _ _ (Pf.atom hcert) ?_
    simp only [Formula.size, Prog.size, numCost, OptimBot, OBot, CooperateBot, DefectBot,
      c_leaf, c_guard, c_node] at hln0 ⊢
    omega
  have hmono : Pf (100 * (Nat.log2 k + Nat.log2 K) + 20000)
      (.impl (.box (2 * c_leaf + c_guard K + c_guard k + 4 * c_node)
                (.plays OBot (OptimBot k K) Action.D))
             (.box k (.plays OBot (OptimBot k K) Action.D))) := by
    refine Pf.boxMono _ k _ _ hn0le ?_
    simp only [Formula.size, Prog.size, numCost, OptimBot, OBot, CooperateBot, DefectBot,
      c_leaf, c_guard, c_node] at hln0 ⊢
    omega
  refine Pf.mp _ _ _ _ hmono hb1 ?_
  simp only [Formula.size, Prog.size, numCost, OptimBot, OBot, CooperateBot, DefectBot]
  omega

end PD.Theorems

