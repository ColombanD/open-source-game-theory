import PrisonersDilemma.Bots.CupodBot
import PrisonersDilemma.Bots.DefectBot
import PrisonersDilemma.Axioms
import PrisonersDilemma.Theorems.ProofSearch
import PrisonersDilemma.Theorems.Helpers

open PD
open PD.Axioms
open PD.Bots

namespace PD.Theorems

theorem llm_outcome_CupodBot_vs_DefectBot (n : Nat) :
    ∃ k, outcome (n+2) (CupodBot k) DefectBot = some (.D, .D) := by
  -- Step 1: DefectBot plays D against CupodBot 0 (trivially).
  have h0 : ∃ m, play m DefectBot (CupodBot 0) = some .D := ⟨1, rfl⟩
  obtain ⟨w, hw⟩ := witness_complete_plays DefectBot (CupodBot 0) .D h0
  -- Step 2: transport witness to CupodBot K with K = witnessChars w.
  let Φ : Nat → Formula := fun i => Formula.plays DefectBot (CupodBot i) .D
  let K := witnessChars w
  have hLe : 0 ≤ K := Nat.zero_le _
  have hwK : witnessChars w ≤ K := Nat.le_refl _
  have hw' : witnessProves w (Φ 0) := hw
  obtain ⟨w', hw'p, hwK'⟩ := witness_transport_family Φ 0 K hLe w hw' hwK
  have hPS : proofSearch K (Φ K) = true :=
    (proofSearch_spec K (Φ K)).2 ⟨w', hw'p, hwK'⟩
  refine ⟨K, ?_⟩
  -- Step 3: compute the two plays.
  have hA : play (n+2) (CupodBot K) DefectBot = some .D := by
    show eval (n+2) (CupodBot K) DefectBot (CupodBot K) = some .D
    show eval (n+2) (CupodBot K) DefectBot
      (.search K (.plays .opp .self .D) (.const .D) (.const .C)) = some .D
    show (if proofSearch K ((Formula.plays .opp .self .D).subst (CupodBot K) DefectBot)
            then eval (n+1) (CupodBot K) DefectBot (.const .D)
            else eval (n+1) (CupodBot K) DefectBot (.const .C)) = some .D
    have hEq : (Formula.plays Prog.opp Prog.self .D).subst (CupodBot K) DefectBot = Φ K := rfl
    rw [hEq, hPS]
    rfl
  have hB : play (n+2) DefectBot (CupodBot K) = some .D := rfl
  exact outcome_of_plays _ _ _ _ _ hA hB

end PD.Theorems
