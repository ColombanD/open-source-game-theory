import PrisonersDilemma.Program
import PrisonersDilemma.Dynamics
import PrisonersDilemma.Axioms
import PrisonersDilemma.Bots.CooperateBot
import PrisonersDilemma.Bots.CupodBot
import PrisonersDilemma.Theorems.CooperateBot
import PrisonersDilemma.Theorems.DefectBot
import PrisonersDilemma.Bots.DefectBot

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

theorem guard_true (n: Nat) :
    ∃ k, (proofSearch k (.plays DefectBot (CupodBot n) .D) = true) := by
  have h3 := proofSearch_complete
  let φ := Formula
  let ν := (Formula.plays DefectBot (CupodBot n) .D)
  have h1 :  ν.interp := by
    have h2 := interp_DefectBot_plays_D_true
    specialize h2 (CupodBot n)
    exact h2
  specialize h3 ν h1
  obtain ⟨k, hk⟩ := h3
  exists k

/-- Monotonicity of CUPOD bot: If the proof search succeeds with less fuel, it also succeeds with more fuel -/
theorem CUPOD_monotonicity (k₁ k₂ : Nat) (bot : Prog) (a : Action) :
    k₁ ≤ k₂ → proofSearch k₁ (.plays bot (CupodBot k₁) a) = true → proofSearch k₂ (.plays bot (CupodBot k₂) a) = true := sorry

theorem guard_true_same_k :
  ∃ k, proofSearch k (.plays DefectBot (CupodBot k) .D) = true := sorry

/-- An example of the formula being incorect -/
theorem CUPOD_vs_CB (k fuel : Nat):
    outcome (fuel + 2) (CupodBot k) CooperateBot = some (.C, .C) := by
  -- Left side: CUPOD executes its `.search` guard. The guard is false by the
  -- lemma above, so the `search` falls through to the final `.const .C` branch.
  have hA : play (fuel + 2) (CupodBot k) CooperateBot = some .C := by
    show eval (fuel + 2) (CupodBot k) CooperateBot (CupodBot k) = some .C
    -- `guard_false` tells us the proof search for “CooperateBot plays D” fails.
    -- Once we unfold the bot, the remaining `simp` can simplify the search node
    -- and the constant branch all the way down to `.C`.
    have hg := guard_false k
    unfold CupodBot at hg ⊢
    simp [eval, Prog.subst, Formula.subst, hg]
  -- Right side: CooperateBot is definitionally the constant `.C` bot.
  have hB : play (fuel + 2) CooperateBot (CupodBot k) = some .C := rfl
  -- Finally, `outcome` just packages the two `play` results together.
  simp [outcome, hA, hB]

/-- An example of the formula being correct -/
theorem CUPOD_vs_DB (k fuel : Nat):
  outcome (fuel + 2) (CupodBot k) DefectBot = some (.D, .D) := sorry

end PDNew.Theorems
