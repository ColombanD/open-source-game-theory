import PrisonersDilemma.Bots.CooperateBot
import PrisonersDilemma.Bots.CupodBot
import PrisonersDilemma.Dynamics
import PrisonersDilemma.Axioms
import PrisonersDilemma.Theorems.ProofSearch

open PD
open PD.Axioms
open PD.Bots
namespace PD.Theorems

theorem interp_CooperateBot_plays_D_false (k : Nat) :
    ¬ (Formula.plays CooperateBot (CupodBot k) .D).interp := by
  intro ⟨n, h⟩
  cases n with
  | zero => simp [play, eval] at h
  | succ m => simp [play, eval, CooperateBot] at h

theorem proofSearch_false_CooperateBot_plays_D (k : Nat) :
    proofSearch k (.plays CooperateBot (CupodBot k) .D) = false := by
  cases h : proofSearch k (.plays CooperateBot (CupodBot k) .D) with
  | true => exact absurd (proofSearch_sound _ _ h) (interp_CooperateBot_plays_D_false k)
  | false => rfl

theorem llm_outcome_CooperateBot_vs_CupodBot (n k : Nat) :
    outcome (n+2) CooperateBot (CupodBot k) = some (.C, .C) := by
  have hG := proofSearch_false_CooperateBot_plays_D k
  have hA : play (n+2) CooperateBot (CupodBot k) = some .C := rfl
  have hB : play (n+2) (CupodBot k) CooperateBot = some .C := by
    show eval (n+2) (CupodBot k) CooperateBot (CupodBot k) = some .C
    unfold CupodBot at hG ⊢
    simp [eval, Prog.subst, Formula.subst, hG]
  simp [outcome, hA, hB]

end PD.Theorems
