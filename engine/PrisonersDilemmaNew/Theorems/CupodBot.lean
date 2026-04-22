import PrisonersDilemmaNew.Program
import PrisonersDilemmaNew.Dynamics
import PrisonersDilemmaNew.Theorems.Axioms
import PrisonersDilemmaNew.Bots.CooperateBot
import PrisonersDilemmaNew.Bots.CupodBot
import PrisonersDilemmaNew.Theorems.CooperateBot

open PDNew
open PDNew.Axioms
open PDNew.Bots
namespace PDNew.Theorems


-- This is the contrapositive of soundness, wrapped in a bool case split.
theorem guard_false (k : Nat) :
    proofSearch k (.plays CooperateBot (CupodBot k) .D) = false := by
  cases h : proofSearch k (.plays CooperateBot (CupodBot k) .D) with
  | true  => exact absurd (proofSearch_sound _ _ h)
                          (interp_CooperateBot_plays_D_false _)
  | false => rfl

-- Main theorem.
theorem CUPOD_vs_CB (k fuel : Nat) (hfuel : 2 ≤ fuel) :
    outcome fuel (CupodBot k) CooperateBot = some (.C, .C) := by
  -- We first rewrite `fuel` as `n + 2` so the evaluator has exactly enough fuel
  -- to unfold the search step and then evaluate the chosen branch.
  obtain ⟨n, rfl⟩ : ∃ n, fuel = n + 2 := ⟨fuel - 2, by omega⟩
  -- Left side: CUPOD executes its `.search` guard. The guard is false by the
  -- lemma above, so the `search` falls through to the final `.const .C` branch.
  have hA : play (n + 2) (CupodBot k) CooperateBot = some .C := by
    show eval (n + 2) (CupodBot k) CooperateBot (CupodBot k) = some .C
    -- `guard_false` tells us the proof search for “CooperateBot plays D” fails.
    -- Once we unfold the bot, the remaining `simp` can simplify the search node
    -- and the constant branch all the way down to `.C`.
    have hg := guard_false k
    unfold CupodBot at hg ⊢
    simp [eval, Prog.subst, Formula.subst, hg]
  -- Right side: CooperateBot is definitionally the constant `.C` bot.
  have hB : play (n + 2) CooperateBot (CupodBot k) = some .C := rfl
  -- Finally, `outcome` just packages the two `play` results together.
  simp [outcome, hA, hB]

end PDNew.Theorems
