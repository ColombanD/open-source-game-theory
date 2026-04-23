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
theorem CUPOD_monotonicity (n k : Nat) (bot : Prog) (a : Action) :
    n ≤ k →
    proofSearch k (.plays bot (CupodBot n) a) = true →
    proofSearch k (.plays bot (CupodBot k) a) = true := sorry

theorem guard_true_same_k :
    ∃ k, proofSearch k (.plays DefectBot (CupodBot k) .D) = true := by
  have h := guard_true
  obtain ⟨k, hk⟩ := h 0 -- we can pick any n, so we pick 0 for simplicity; k is the corresponding k from the lemma.
  refine ⟨k, ?_⟩ -- use the same k for the conclusion
  exact CUPOD_monotonicity 0 k DefectBot .D (Nat.zero_le k) hk

  -- split the cases on whether k is less than n or not.
  -- If k < n, then we can use monotonicity of proofsearch to show that the proof search also succeeds for k.
  -- If k >= n, then we use monotonicity of Cupod: if Cupod(n) is succesful, then so is Cupod(n + m) for any m.

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
theorem CUPOD_vs_DB (fuel : Nat):
    ∃ k, outcome (fuel + 2) (CupodBot k) DefectBot = some (.D, .D) := by
  obtain ⟨k, hk⟩ := guard_true_same_k
  refine ⟨k, ?_⟩

  have hA : play (fuel + 2) (CupodBot k) DefectBot = some .D := by
    show eval (fuel + 2) (CupodBot k) DefectBot (CupodBot k) = some .D
    unfold CupodBot at hk ⊢
    simp [eval, Prog.subst, Formula.subst, hk]

  have hB : play (fuel + 2) DefectBot (CupodBot k) = some .D := by
    simpa [Nat.add_assoc] using (play_DefectBot (fuel + 1) (CupodBot k))

  simp [outcome, hA, hB]


end PDNew.Theorems
