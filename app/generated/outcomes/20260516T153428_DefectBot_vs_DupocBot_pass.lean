import PrisonersDilemma.Bots.DefectBot
import PrisonersDilemma.Bots.DupocBot
import PrisonersDilemma.Theorems.ProofSearch
import PrisonersDilemma.Axioms
import PrisonersDilemma.Dynamics

open PDNew
open PDNew.Axioms
open PDNew.Bots

namespace PDNew.Theorems

private theorem interp_DefectBot_plays_C_false_local (q : Prog) :
    ¬ (Formula.plays DefectBot q .C).interp := by
  rintro ⟨n, hn⟩
  cases n with
  | zero => simp [play, eval] at hn
  | succ m =>
    simp [play, eval, DefectBot] at hn

private theorem proofSearch_false_DefectBot_C_local (k : Nat) (q : Prog) :
    proofSearch k (.plays DefectBot q .C) = false := by
  cases h : proofSearch k (.plays DefectBot q .C) with
  | true => exact absurd (proofSearch_sound _ _ h) (interp_DefectBot_plays_C_false_local _)
  | false => rfl

theorem llm_outcome_DefectBot_vs_DupocBot (n k : Nat) :
    outcome (n+2) DefectBot (DupocBot k) = some (.D, .D) := by
  have hg := proofSearch_false_DefectBot_C_local k (DupocBot k)
  have hA : play (n+2) DefectBot (DupocBot k) = some .D := by
    show eval (n+2) DefectBot (DupocBot k) DefectBot = some .D
    simp [eval, DefectBot]
  have hB : play (n+2) (DupocBot k) DefectBot = some .D := by
    show eval (n+2) (DupocBot k) DefectBot (DupocBot k) = some .D
    unfold DupocBot at hg ⊢
    simp [eval, Prog.subst, Formula.subst, hg]
  simp [outcome, hA, hB]

end PDNew.Theorems
