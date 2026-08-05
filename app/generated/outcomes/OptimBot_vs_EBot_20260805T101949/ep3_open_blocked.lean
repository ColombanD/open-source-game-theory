import PrisonersDilemma.Bots.LlmGenerations.OptimBot
import PrisonersDilemma.Bots.MirrorBot
import PrisonersDilemma.Dynamics
import PrisonersDilemma.Base.Helpers
import PrisonersDilemma.BaseTheorems

open PD
open PD.Bots
open PD.BaseTheorems
namespace PD.Theorems

example (k K : Nat) :
    Pf (K + 2 * k + 100 * (Nat.log2 k + Nat.log2 K) + 5000)
      (.impl (.box k (.plays (.bot MirrorBot) (OptimBot k K) Action.C))
        (.impl (.neg (.plays (OptimBot k K) (.bot MirrorBot) Action.D))
          (.impl (.box k (.plays (.bot MirrorBot) (OptimBot k K) Action.C))
            (.impl (.box K (.plays (OptimBot k K) (.bot MirrorBot) Action.C))
              (.plays (OptimBot k K) (.bot MirrorBot) Action.C))))) := by
  have hchain := Pf.searchElseChain
    (.thenL k (.plays .opp .self Action.C)
      (.search k (.plays .opp .self Action.C)
        (.search K (.plays .self .opp Action.C) (.const Action.C)
          (.search k (.plays .opp .self Action.D)
            (.search K (.plays .self .opp Action.D) (.const Action.D) (.const Action.C))
            (.const Action.C)))
        (.search k (.plays .opp .self Action.D)
          (.search K (.plays .self .opp Action.D) (.const Action.D) (.const Action.C))
          (.const Action.C))))
    [ .elseL K (.self) (.opp) Action.D (.const Action.D),
      .thenL k (.plays .opp .self Action.C)
        (.search k (.plays .opp .self Action.D)
          (.search K (.plays .self .opp Action.D) (.const Action.D) (.const Action.C))
          (.const Action.C)),
      .thenL K (.plays .self .opp Action.C)
        (.search k (.plays .opp .self Action.D)
          (.search K (.plays .self .opp Action.D) (.const Action.D) (.const Action.C))
          (.const Action.C)) ]
    Action.C (OptimBot k K) (.bot MirrorBot)
    (by unfold OptimBot; rfl)
    (k := K + 2 * k + 100 * (Nat.log2 k + Nat.log2 K) + 5000)
    (by
      simp only [layersCost, layerCost, guards2, guard2, implChain, List.foldr,
        Formula.size, Prog.size, Formula.subst, Prog.subst, numCost, c_guard,
        c_node, OptimBot, MirrorBot]
      have hlk := log2_le_self k
      have hlK := log2_le_self K
      omega)
  simp only [guards2, guard2, implChain, List.foldr, Formula.subst, Prog.subst] at hchain
  exact hchain

end PD.Theorems

