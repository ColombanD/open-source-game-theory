import PrisonersDilemma.Program
import PrisonersDilemma.Dynamics
import PrisonersDilemma.Axioms
import PrisonersDilemma.Bots.CooperateBot
import PrisonersDilemma.Bots.CupodBot
import PrisonersDilemma.Theorems.CooperateBot
import PrisonersDilemma.Theorems.DefectBot
import PrisonersDilemma.Bots.DefectBot
import PrisonersDilemma.Theorems.ProofSearch

open PDNew
open PDNew.Axioms
open PDNew.Bots
namespace PDNew.Theorems

/-- Monotonicity of CUPOD bot: If the proof search succeeds with less fuel, it also succeeds with more fuel -/
theorem CupodBot_monotonicity (n k : Nat) :
    n ≤ k →
    proofSearch k (.plays DefectBot (CupodBot n) .D) = true →
    proofSearch k (.plays DefectBot (CupodBot k) .D) = true := by
  intro hle hnk
  let Φ : Nat → Formula := fun i => Formula.plays DefectBot (CupodBot i) .D
  obtain ⟨w, hw, hwk⟩ := (proofSearch_spec k (Φ n)).1 hnk
  obtain ⟨w', hw', hwk'⟩ := witness_transport_family Φ n k hle w hw hwk
  exact (proofSearch_spec k (Φ k)).2 ⟨w', hw', hwk'⟩


/-- Proof search is false for CooperateBot -/
theorem proofSearch_false_for_CooperateBot (k : Nat) :
    proofSearch k (.plays CooperateBot (CupodBot k) .D) = false := by
  cases h : proofSearch k (.plays CooperateBot (CupodBot k) .D) with
  | true  => exact absurd (proofSearch_sound _ _ h)
                          (interp_CooperateBot_plays_D_false _)
  | false => rfl

/-- Proof search k is true for DefectBot vs Cupod n, but n ≠ k -/
theorem proofSearch_true_for_DefectBot_different_k (n: Nat) :
    ∃ k, (proofSearch k (.plays DefectBot (CupodBot n) .D) = true) := by
  let φ := Formula
  let ν := (Formula.plays DefectBot (CupodBot n) .D)
  have h1 :  ν.interp := by
    have h2 := interp_DefectBot_plays_D_true
    specialize h2 (CupodBot n)
    exact h2
  have h3 := proofSearch_complete
  specialize h3 ν h1
  obtain ⟨k, hk⟩ := h3
  exists k

/-- Proof search k is true for DefectBot vs Cupod k -/
theorem proofSearch_true_for_DefectBot :
    ∃ k, proofSearch k (.plays DefectBot (CupodBot k) .D) = true := by
  have h := proofSearch_true_for_DefectBot_different_k
  obtain ⟨k, hk⟩ := h 0 -- we can pick any n, so we pick 0 for simplicity; k is the corresponding k from the lemma.
  refine ⟨k, ?_⟩ -- use the same k for the conclusion
  exact CupodBot_monotonicity 0 k (Nat.zero_le k) hk


/-- CupodBot vs CooperateBot: uses proof search being false -/
theorem CupodBot_vs_CB (k fuel : Nat):
    outcome (fuel + 2) (CupodBot k) CooperateBot = some (.C, .C) := by
  -- Left side: CUPOD executes its `.search` guard. The guard is false by the
  -- lemma above, so the `search` falls through to the final `.const .C` branch.
  have hA : play (fuel + 2) (CupodBot k) CooperateBot = some .C := by
    show eval (fuel + 2) (CupodBot k) CooperateBot (CupodBot k) = some .C
    -- `guard_false` tells us the proof search for “CooperateBot plays D” fails.
    -- Once we unfold the bot, the remaining `simp` can simplify the search node
    -- and the constant branch all the way down to `.C`.
    have hg := proofSearch_false_for_CooperateBot k
    unfold CupodBot at hg ⊢
    simp [eval, Prog.subst, Formula.subst, hg]
  -- Right side: CooperateBot is definitionally the constant `.C` bot.
  have hB : play (fuel + 2) CooperateBot (CupodBot k) = some .C := rfl
  -- Finally, `outcome` just packages the two `play` results together.
  simp [outcome, hA, hB]

/-- CupodBot vs DefectBot: uses proof search being true -/
theorem CupodBot_vs_DB (fuel : Nat):
    ∃ k, outcome (fuel + 2) (CupodBot k) DefectBot = some (.D, .D) := by
  obtain ⟨k, hk⟩ := proofSearch_true_for_DefectBot
  refine ⟨k, ?_⟩

  have hA : play (fuel + 2) (CupodBot k) DefectBot = some .D := by
    show eval (fuel + 2) (CupodBot k) DefectBot (CupodBot k) = some .D
    unfold CupodBot at hk ⊢
    simp [eval, Prog.subst, Formula.subst, hk]

  have hB : play (fuel + 2) DefectBot (CupodBot k) = some .D := by
    simpa [Nat.add_assoc] using (play_DefectBot (fuel + 1) (CupodBot k))

  simp [outcome, hA, hB]


end PDNew.Theorems
