import PrisonersDilemma.Bots.CupodBot
import PrisonersDilemma.Bots.DupocBot
import PrisonersDilemma.Dynamics
import PrisonersDilemma.Axioms
import PrisonersDilemma.Theorems.Helpers
import PrisonersDilemma.Theorems.ProofSearch

open PDNew
open PDNew.Bots
open PDNew.Axioms

namespace PDNew.Theorems

/-- CupodBot vs DupocBot: the matchup's outcome is oracle-dependent (three of
the four action pairs are consistent with the axioms; only (D,C) is ruled out
by soundness). When neither bot's bounded proof search succeeds, CupodBot
falls through to cooperate and DupocBot falls through to defect, giving
(C, D). The two `proofSearch _ = false` hypotheses make this assumption
explicit. -/
theorem llm_outcome_CupodBot_vs_DupocBot (n k₁ k₂ : Nat)
    (h₁ : proofSearch k₁
      ((Formula.plays Prog.opp Prog.self Action.D).subst (CupodBot k₁) (DupocBot k₂)) = false)
    (h₂ : proofSearch k₂
      ((Formula.plays Prog.opp Prog.self Action.C).subst (DupocBot k₂) (CupodBot k₁)) = false) :
    outcome (n+2) (CupodBot k₁) (DupocBot k₂) = some (.C, .D) := by
  have hA : play (n+2) (CupodBot k₁) (DupocBot k₂) = some .C := by
    show eval (n+2) (CupodBot k₁) (DupocBot k₂) (CupodBot k₁) = some .C
    have h1' : proofSearch k₁
        ((Formula.plays Prog.opp Prog.self Action.D).subst
          (Prog.search k₁ (Formula.plays Prog.opp Prog.self Action.D) (Prog.const Action.D) (Prog.const Action.C))
          (DupocBot k₂)) = false := h₁
    unfold CupodBot
    simp only [eval, h1']
    rfl
  have hB : play (n+2) (DupocBot k₂) (CupodBot k₁) = some .D := by
    show eval (n+2) (DupocBot k₂) (CupodBot k₁) (DupocBot k₂) = some .D
    have h2' : proofSearch k₂
        ((Formula.plays Prog.opp Prog.self Action.C).subst
          (Prog.search k₂ (Formula.plays Prog.opp Prog.self Action.C) (Prog.const Action.C) (Prog.const Action.D))
          (CupodBot k₁)) = false := h₂
    unfold DupocBot
    simp only [eval, h2']
    rfl
  simp [outcome, hA, hB]

end PDNew.Theorems
